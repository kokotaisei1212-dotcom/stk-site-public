"""Is this permission STK's?

    python3 stk_verify.py <file.jsonl> [keys.json] [rules.json]
    python3 stk_verify.py --from-file <file.jsonl>      (nothing of STK needed: the keys and rules the file kept)
    python3 stk_verify.py --receipt <receipt.json> [keys.json]
        (a receipt and its signature only, no row and no random bytes: {"receipt": {...}, "sig": "..."}. It tells whether
        STK signed this seal, at this time, under this version of the rules. It cannot tell what the row was: the intent
        and the trigger are not in a receipt. With keys.json, a copy of STK's public keys, nothing goes over the network.)

Needs: pip install cryptography

A line of the file, as stk.py or stk.mjs keeps it:

    {"row": "<your row, as the text that was sealed>", "nonce": "<the 32 random bytes, 64 hex>",
     "receipt": {"v", "seal", "time_ms", "recorded_ms", "rule_version", "account", "which_key", "kid"}, "sig": "<base64>"}

A receipt of version 2 has two times: recorded_ms, when the library recorded the action (the company's own claim),
and time_ms, when STK signed (what STK attests). They are the same moment unless the seal waited in the library's
queue while STK could not be reached; then both are shown. A receipt of version 1 has time_ms only, without recorded_ms.

Each line is checked alone, three things, no secret needed:

    1. The seal.       SHA-256 of the 32 random bytes followed by the row's text is the receipt's seal.
                       A row changed after it was sealed does not match.
    2. The signature.  The public key of the receipt's kid (STK's, not made invalid) checks the signature over the
                       receipt's values in the order above, as a JSON array with no spaces.
    3. The rules.      The version of the rules named in the receipt (its text signed by STK) answers finish for the
                       row's intent and trigger. A Never intent, a closed one, or a row only an older version passes,
                       does not.

Public keys: https://api.stk-evidence.com/v1/rules?keys=1 (or keys.json). Rules: /v1/rules?history=1 (or rules.json).
Other lines in the file (the rules applied, a public key, a person joining, not_listed, not_told, to_tell, grant) are not
permissions and are skipped. A line marked "cancelled" was told to STK as a person joining: shown, not counted as a failure."""
import base64, hashlib, json, re, sys, urllib.request
from functools import lru_cache

from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey

RECEIPT = ("v", "seal", "time_ms", "rule_version", "account", "which_key", "kid")
RECEIPT2 = ("v", "seal", "time_ms", "recorded_ms", "rule_version", "account", "which_key", "kid")
NOT_PERMISSIONS = {
    "rules": "the rules applied (not a permission)",
    "key": "a public key saved (not a permission)",
    "joined": "a person joined, told to STK (a count, not a permission)",
    "not_listed": "an intent on no list of the rules, kept for your own count (not a permission)",
    "not_told": "a person joining STK refused to be told of, or (files before 2026-11-22) a late permission STK could not be told about: it stays billed (not a permission line)",
    "grant": "a grant from STK's last answer, kept for a restart (not a permission)",
    "to_tell": "a person joining that STK could not be told yet: told as soon as STK answers (its joined line has of)",
    "queued": "a seal waiting for STK, finished under a grant (its signed line follows when STK signs it)",
    "not_signed": "a queued seal STK did not sign (not a permission)",
    "dequeued": "a queued seal taken off before STK signed it: a person joined (not a permission)",
}


def fields(rc):
    """The receipt's fields in the order STK signs them, by its version."""
    return RECEIPT2 if rc.get("v") == 2 else RECEIPT


def _utc(ms):
    import datetime
    return datetime.datetime.fromtimestamp(ms / 1000, datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%S.%f")[:-3] + " UTC"


def times(rc):
    """The two times of a receipt, said as they are: what STK attests and what the library recorded."""
    if rc.get("v") != 2:
        return "signed by STK at " + _utc(rc["time_ms"])
    gap = rc["time_ms"] - rc["recorded_ms"]
    out = "signed by STK at " + _utc(rc["time_ms"]) + "; recorded by the library at " + _utc(rc["recorded_ms"]) + " (the company's claim)"
    if gap >= 1000:
        out += f"; recorded {gap / 1000:.1f} s before STK signed: it waited in the library's queue"
    elif gap <= -1000:
        out += f"; recorded {-gap / 1000:.1f} s after STK signed, by the library's clock"
    return out


# ---- the rules ----------------------------------------------------------------------------------------------------------
@lru_cache(maxsize=64)
def lists(text):
    """(Never, Permitted, Closed) of a version's text."""
    def one(name):
        m = re.search(r"^" + name + r" \((\d+)\): (.*)$", text, re.M)
        items = [] if m.group(2) == "none" else [x.strip().split(" (closed")[0] for x in m.group(2).split(",")]
        if len(items) != int(m.group(1)):
            raise ValueError("the rules text does not read as STK's")
        return frozenset(items)
    return one("Never"), one("Permitted"), one("Closed")


def decide(text, intent, trigger):
    """The rules, read from their text, as stk.py reads them: "finish" or "escalate"."""
    never, permitted, closed = lists(text)
    if isinstance(intent, str) and intent.startswith("conversation.") and intent[13:] in never | permitted | closed:
        intent = intent[13:]                    # Rule 5: the full name, with its domain, is the name listed
    if trigger == "unknown" and intent in permitted and intent not in never and intent not in closed:
        return "finish"
    return "escalate"


# ---- jurisdictions (from Rule 9) ------------------------------------------------------------------------------------------
_JUR = re.compile(r"[A-Z]{2}(-[A-Z0-9]{1,3})?")


def jurisdictions(where):
    """The codes given, as the rules read them (UK is GB), sorted; None when none is given or one is not a code."""
    if isinstance(where, str):
        where = [where]
    if not isinstance(where, (list, tuple)) or not where:
        return None
    out = set()
    for c in where:
        if not isinstance(c, str):
            return None
        c = c.strip().upper()
        if c == "UK" or c.startswith("UK-"):
            c = "GB" + c[2:]
        if not _JUR.fullmatch(c):
            return None
        out.add(c)
    return sorted(out)


def _items(text, head):
    m = re.search(r"^" + re.escape(head) + r"[^\n]*\n((?:- [^\n]*\n?)*)", text, re.M)
    return None if m is None else [x[2:] for x in m.group(1).splitlines()]


def decide_where(text, intent, trigger, where):
    """(answer, read): the rules for the jurisdictions given. read is False when none is given, one is not a code, one
    has not been read for the intent's subject, or the rules are older than Rule 9: the answer is then decide's, the
    strictest. A jurisdiction's answer is never stricter than that."""
    strict = decide(text, intent, trigger)
    codes = jurisdictions(where)
    laws = _items(text, "The jurisdictions of the laws beside each intent on the Never list")
    subjects, read = _items(text, "The subject of each intent:"), _items(text, "Read (")
    if codes is None or laws is None or subjects is None or read is None:
        return strict, False
    subject = {}
    for x in subjects:
        sj, _, names = x.partition(": ")
        for n in names.split(", "):
            subject[n] = sj
    i = intent[13:] if isinstance(intent, str) and intent.startswith("conversation.") and intent[13:] in subject else intent
    sj = subject.get(i) if isinstance(i, str) else None
    done = {}
    for x in read:
        m = re.match(r"([a-z]+) in ([A-Z0-9, -]+): ", x)
        if m:
            done.setdefault(m.group(1), set()).update(m.group(2).split(", "))
    if sj is None or not all(c in done.get(sj, ()) for c in codes):
        return strict, False
    if strict == "finish" or trigger != "unknown":
        return strict, True
    beside = {k: v.split(", ") for k, _, v in (x.partition(": ") for x in laws)}
    if i not in beside:                         # closed, other, on no list: as the strictest
        return strict, True
    named = any(c == g or c.split("-")[0] == g or g.split("-")[0] == c for c in codes for g in beside[i])
    return ("escalate" if named else "finish"), True


# ---- signatures ---------------------------------------------------------------------------------------------------------
@lru_cache(maxsize=4096)
def _public_key(b64):
    return Ed25519PublicKey.from_public_bytes(base64.b64decode(b64))


def _ok(public_key_b64, sig, body):
    try:
        _public_key(public_key_b64).verify(base64.b64decode(sig), body)
        return True
    except Exception:
        return False


def _json(values):
    return json.dumps(values, ensure_ascii=False, separators=(",", ":")).encode("utf-8")


def rules_checked(versions, keys):
    """{version: text} of the versions of the rules whose text STK's signature checks."""
    out = {}
    for v in versions:
        k = keys.get(v.get("kid"))
        body = _json(["stk-rules", v["version"], v["published"], v["text"]])
        if k and not k.get("invalid") and v.get("sig") and _ok(k["public_key"], v["sig"], body):
            out[v["version"]] = v["text"]
    return out


# ---- one line -------------------------------------------------------------------------------------------------------------
def check(line, keys, rules):
    """"STK's", or why not. keys: {kid: public key}; rules: {version: text}, from rules_checked."""
    for kind, what in NOT_PERMISSIONS.items():
        if kind in line:
            return what
    try:
        row_text, nonce, rc, sig = line["row"], bytes.fromhex(line["nonce"]), line["receipt"], line["sig"]
        row = json.loads(row_text)
    except Exception:
        return "NOT STK's: not a line as stk.py keeps it"
    # 1. the seal
    if hashlib.sha256(nonce + row_text.encode("utf-8")).hexdigest() != rc.get("seal"):
        return "NOT STK's: the row does not match its seal (changed after it was sealed)"
    # 2. the signature
    k = keys.get(rc.get("kid"))
    if not k:
        return "NOT STK's: not STK's key"
    if k.get("invalid"):
        return "NOT STK's: its key was made invalid on " + k["invalid"]
    if set(rc) != set(fields(rc)) or not _ok(k["public_key"], sig, _json([rc[f] for f in fields(rc)])):
        return "NOT STK's: the receipt or its signature was changed"
    # 3. the rules
    text = rules.get(rc["rule_version"])
    if text is None:
        return "NOT STK's: no signed rules of version " + str(rc["rule_version"])[:12]
    said = row.get("jurisdiction") if isinstance(row, dict) else None    # from Rule 9: the jurisdictions ask_where was given
    if (decide(text, row.get("intent"), row.get("trigger")) if said is None
            else decide_where(text, row.get("intent"), row.get("trigger"), said)[0]) != "finish":
        if line.get("cancelled"):
            return "cancelled: told to STK as a person joining, not billed"
        return "NOT a permission: the rules of " + rc["rule_version"][:12] + " do not answer finish for this row"
    late = rc.get("v") == 2 and abs(rc["time_ms"] - rc["recorded_ms"]) >= 1000
    if rc.get("which_key") != "live":
        return "STK's, of a test key: not a live permission, never billed" + ("; " + times(rc) if late else "")
    return "STK's" + ("; " + times(rc) if late else "")


# ---- the command ------------------------------------------------------------------------------------------------------------
def _load(arg, path):
    if arg:
        return json.load(open(arg))
    req = urllib.request.Request("https://api.stk-evidence.com" + path, headers={"User-Agent": "stk-verify"})
    return json.load(urllib.request.urlopen(req, timeout=20))


def check_receipt(receipt, sig, keys):
    """A receipt and its signature, without the row: "STK signed ..." or why not. Says nothing of the row."""
    k = keys.get((receipt or {}).get("kid"))
    if not k:
        return "NOT STK's: not STK's key"
    if k.get("invalid"):
        return "NOT STK's: its key was made invalid on " + k["invalid"]
    if set(receipt) != set(fields(receipt)) or not _ok(k["public_key"], sig, _json([receipt[f] for f in fields(receipt)])):
        return "NOT STK's: the receipt or its signature was changed"
    return (f"STK signed the seal {receipt['seal']} under the rules of version {receipt['rule_version']}, for the account "
            f"{receipt['account']} ({receipt['which_key']} key): {times(receipt)}. What the row was cannot be told from a receipt.")


def main(argv):
    a = argv + [None, None, None]
    if a[1] == "--receipt":
        x = json.load(open(a[2], encoding="utf-8"))
        keys = {k["kid"]: k for k in _load(a[3], "/v1/rules?keys=1")["keys"]}
        r = check_receipt(x.get("receipt"), x.get("sig"), keys)
        print(r)
        return 1 if r.startswith("NOT") else 0
    if a[1] == "--from-file":
        del a[1]
        saved = [json.loads(t) for t in open(a[1], encoding="utf-8") if t.strip()]
        keys = {x["key"]["kid"]: x["key"] for x in saved if "key" in x}
        rules = rules_checked([x["rules"] for x in saved if "rules" in x], keys)
    else:
        keys = {k["kid"]: k for k in _load(a[2], "/v1/rules?keys=1")["keys"]}
        rules = rules_checked(_load(a[3], "/v1/rules?history=1")["versions"], keys)
    bad = 0
    for n, text in enumerate(open(a[1], encoding="utf-8"), 1):
        if not text.strip():
            continue
        line = json.loads(text)
        if any(k in line for k in NOT_PERMISSIONS):
            continue
        r = check(line, keys, rules)
        bad += r.startswith("NOT")
        print(n, r)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
