"""STK: ask before your AI hands a conversation to a person. https://stk-evidence.com/docs

    import stk
    if stk.ask(intent, trigger, conversation_id=cid) == "finish":
        ...  # your AI goes on with the conversation
    else:
        ...  # hand it to a person, as your code does today
    stk.joined(cid)   # a person joined a conversation that got finish: that permission is taken off its day's bill

trigger: a trigger of the rules' Triggers list (https://stk-evidence.com/rules-full#triggers) that happened in the
conversation, each defined there word for word:
  customer_asked, distressed, angry, bereavement, threat, legal_claim
or unknown when none of them happened: the only one the rules can answer finish to.

This file decides, here, on your side, from STK's public rules (GET /v1/rules, the same for every company, signed by
STK). STK receives nothing of the conversation. Only on finish does it call STK, and it sends the seal and the time it recorded the action:
SHA-256 of 32 random bytes and your row. The row is intent and trigger and whatever else you give ask() (any fields);
the row and the random bytes stay here. STK signs the seal with the time and the rules version: that is the
permission, and each one is billed. An unpaid invoice 60 days after its due date, or STK without a published key: no
signature, and ask() returns "escalate".

Each permission is kept as one JSON line in ROWS_DIR/<day>.jsonl (by default ./stk-rows, or STK_ROWS_DIR), before
ask() returns: the row, the random bytes, STK's receipt and signature. Or give ON_ROW a function and it gets each line
instead (a place with no files you keep, like a serverless function). If the folder cannot be written, the line goes
to standard output; if ON_ROW raises, the permission is told to STK as a person joining and ask() returns "escalate".
Lose them and nobody can give them back: STK never had them. Check them: stk_verify.py. An intent on no list of the
rules leaves a not_listed line there, for your own count; STK is not told.

When STK's answer says a newer version of the rules, this file reads the rules again and applies them again; if they
now say escalate, it returns "escalate" and tells STK a person has it, so that permission is not billed. The same
conversation and intent that got finish today (UTC) gets finish again without calling STK (after a restart, today's
file is read again; with ON_ROW only while the process runs). Without an answer within 300 ms, or on any error, ask()
returns "escalate"; if a late answer was a permission, STK is told a person has it, so it is not billed.

Each answer of STK's also brings a grant, signed by STK, for this account and this version of the rules, for 10 minutes. If
STK cannot be reached (no answer within 300 ms, or an error reaching it) while the last grant holds, the rules here say
finish and the queue is not full, ask() returns "finish" and the seal waits in a queue, kept as a queued line; it is
sent as soon as STK answers again, and STK signs it as it signs any seal. The grant gone, or QUEUE_MAX seals waiting:
"escalate", as before. A receipt has two times: recorded_ms, when this file recorded the action (your claim), and
time_ms, when STK signed (what STK attests). They are the same moment unless the seal waited in the queue.

STK's own trouble never reaches your code as an error: ask() returns finish or escalate, and joined() returns. A
starting STK server, or one that cannot read the unpaid state from Stripe, answers 503, and a 429 is the same: STK not
reached, so the grant holds as above. A person joining that STK cannot be told is kept (a to_tell line) and told as
soon as STK answers, also after a restart; told after 00:10 UTC the day after the finish, it stays billed. After the
rules could not be read, ask() escalates at once for RULES_RETRY seconds instead of waiting 2 seconds each time.

Try it without a key: python3 stk.py conversation.order.status unknown   (it reads the public rules and decides; it sends nothing)
Python 3.8 or later, nothing to install."""
import hashlib, json, os, re, secrets, sys, threading, time, urllib.error, urllib.request

KEY = os.environ.get("STK_KEY", "")   # your key, from the environment (STK_KEY): the test key first, the live key when you go live
API = os.environ.get("STK_API", "https://api.stk-evidence.com")
TIMEOUT = 0.3
QUEUE_MAX = 10000      # seals waiting for STK at most; past it, "escalate"
QUEUE_RETRY = 5        # seconds between tries to send the queue, and a person joining STK could not be told yet
RULES_RETRY = 10       # seconds after the rules could not be read in which ask() escalates without trying again
ROWS_DIR = os.environ.get("STK_ROWS_DIR", "stk-rows")
ON_ROW = None          # or a function(line: dict): each line, for your own store
_lock = threading.Lock()
_rules = {}            # the signed rules in use: version, published, text, kid, sig
_finished = {"day": None, "done": set(), "kids": set(), "seals": {}, "yesterday": {}}
GRACE = 600                               # seconds after midnight (UTC) in which STK counts a seal of the day before for its day   # today's (conversation_id, intent) that got finish; keys saved
_asking = {}                              # (conversation_id, intent) being asked now: one call to STK for them
_grant = {}                               # the last grant: g, sig, and until (this process's monotonic clock)
_queue = {}                               # seal -> its queued line, waiting for STK; in the order recorded
_tells = {}                               # id -> a person joining that STK could not be told yet (a to_tell line)
_teller = {"on": False}
_rules_failed = {"at": None}              # when the rules last could not be read (this process's monotonic clock)
_clock = {"offset": 0}                    # ms to add to this machine's clock, if it is more than 30 s from STK's
_sender = {"on": False}


def decide(text, intent, trigger):
    """The rules, read from their text: "finish" or "escalate". (An invoice unpaid 60 days is in STK's Terms: STK does not sign.)"""
    def lst(name):
        m = re.search(r"^" + name + r" \((\d+)\): (.*)$", text, re.M)
        items = [] if m.group(2) == "none" else [x.strip().split(" (closed")[0] for x in m.group(2).split(",")]
        if len(items) != int(m.group(1)):
            raise ValueError("the rules text does not read as STK's")
        return set(items)
    never, permitted, closed = lst("Never"), lst("Permitted"), lst("Closed")
    intent = _named(intent, never | permitted | closed)
    if trigger != "unknown":
        return "escalate"
    if intent in never:
        return "escalate"
    if intent not in never | permitted | closed:
        return "escalate"
    if intent in closed:
        return "escalate"
    return "finish"


def _named(intent, known):
    """An intent's full name, with its domain (conversation.claim.status), is read as the name listed (claim.status)."""
    if isinstance(intent, str) and intent.startswith("conversation.") and intent[13:] in known:
        return intent[13:]
    return intent


def listed(text, intent):
    """The intent is on one of the rules' lists (Never, Permitted, Closed), with or without its domain."""
    for name in ("Never", "Permitted", "Closed"):
        m = re.search(r"^" + name + r" \((\d+)\): (.*)$", text, re.M)
        items = [] if m.group(2) == "none" else [x.strip().split(" (closed")[0] for x in m.group(2).split(",")]
        if intent in items or (isinstance(intent, str) and intent.startswith("conversation.") and intent[13:] in items):
            return True
    return False


def _js_number(x):
    """A float as JavaScript writes it (Number::toString), so stk.py and stk.mjs write the same row."""
    if x == 0:
        return "0"
    if x == int(x) and abs(x) < 1e21:
        return str(int(x))
    m = re.fullmatch(r"(-?)(\d+)(?:\.(\d+))?(?:e([+-]\d+))?", repr(x))
    sign, ip, fp, ex = m.group(1), m.group(2), m.group(3) or "", int(m.group(4) or 0)
    lead = len(ip + fp) - len((ip + fp).lstrip("0"))
    d = (ip + fp).lstrip("0").rstrip("0")
    k, n = len(d), len(ip) + ex - lead
    if k <= n <= 21:
        out = d + "0" * (n - k)
    elif 0 < n <= 21:
        out = d[:n] + "." + d[n:]
    elif -6 < n <= 0:
        out = "0." + "0" * (-n) + d
    else:
        e = n - 1
        out = d[0] + ("." + d[1:] if k > 1 else "") + "e" + ("+" if e >= 0 else "-") + str(abs(e))
    return sign + out


def _str(v):
    t = json.dumps(v, ensure_ascii=False)
    return re.sub("[\ud800-\udfff]", lambda m: "\\u%04x" % ord(m.group()), t)   # a lone surrogate, as JavaScript writes it


def row_text(v):
    """The row as text, one way only, the same in stk.py and stk.mjs: keys sorted by code point, no spaces, Unicode as
    it is, numbers as JavaScript writes them, NaN and infinities as null. Its bytes are what is sealed."""
    if v is None or (isinstance(v, float) and (v != v or v in (float("inf"), float("-inf")))):
        return "null"
    if v is True or v is False:
        return "true" if v else "false"
    if isinstance(v, int):
        return str(v)
    if isinstance(v, float):
        return _js_number(v)
    if isinstance(v, str):
        return _str(v)
    if isinstance(v, dict):
        return "{" + ",".join(_str(str(k)) + ":" + row_text(v[k]) for k in sorted(v, key=str)) + "}"
    if isinstance(v, (list, tuple)):
        return "[" + ",".join(row_text(x) for x in v) + "]"
    raise TypeError("a row holds text, numbers, true, false, null, lists and objects only")


def _today():
    return time.strftime("%Y-%m-%d", time.gmtime(time.time()))


def _http(method, path, body=None, key=True, timeout=10):
    req = urllib.request.Request(API + path, method=method, data=None if body is None else json.dumps(body).encode(),
                                 headers=dict({"Content-Type": "application/json", "User-Agent": "stk.py"}, **({"X-STK-Key": KEY} if key else {})))
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return json.load(r)


def _now_ms():
    return int(time.time() * 1000) + _clock["offset"]


def _grant_ok(version):
    with _lock:
        g = _grant.get("g")
        return bool(g) and g["rule_version"] == version and time.monotonic() < _grant["until"] and len(_queue) < QUEUE_MAX


def _keep_grant(a):
    g, sig = a.get("grant"), a.get("grant_sig")
    if g and sig:
        with _lock:
            _grant.update(g=g, sig=sig, until=time.monotonic() + (g["expires_ms"] - g["issued_ms"]) / 1000)


def rules(fresh=False, timeout=10):
    """The rules in use, read from STK when there are none yet or fresh is asked."""
    with _lock:
        if _rules and not fresh:
            return dict(_rules)
    r = _http("GET", "/v1/rules", key=False, timeout=timeout)
    decide(r["text"], "", "unknown")          # it reads as STK's rules, or this raises
    with _lock:
        new = r["version"] != _rules.get("version")
        _rules.clear(); _rules.update(r)
    if new:
        _write({"rules": r})                  # the signed rules applied, kept with the rows
    return dict(r)


def _write(line):
    if ON_ROW is not None:
        ON_ROW(line)
        return
    text = json.dumps(line, ensure_ascii=False, separators=(",", ":"))
    try:
        os.makedirs(ROWS_DIR, exist_ok=True)
        fd = os.open(os.path.join(ROWS_DIR, _today() + ".jsonl"), os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o644)
        try:                                  # one write of the whole line, appended: servers sharing the file never mix lines
            data = (text + "\n").encode("utf-8")
            if os.write(fd, data) != len(data):
                raise OSError("short write")
        finally:
            os.close(fd)
    except OSError:
        print(text, file=sys.stdout, flush=True)


def _done_today():
    d = _today()
    with _lock:
        if _finished["day"] != d:             # a new day, or the first ask since this process started
            if _finished["day"] is not None:  # yesterday's seals, for a person told in the first minutes after midnight
                _finished["yesterday"] = _finished["seals"]
            _finished["day"], _finished["done"], _finished["kids"], _finished["seals"] = d, set(), set(), {}
            _finished["told"] = set()
            if ON_ROW is None:
                taken_off = set()
                try:
                    with open(os.path.join(ROWS_DIR, d + ".jsonl"), encoding="utf-8") as f:
                        for text in f:
                            try:
                                line = json.loads(text)
                                if "key" in line:
                                    _finished["kids"].add(line["key"]["kid"])
                                for k in ("joined", "to_tell"):
                                    if isinstance(line.get(k), dict) and line[k].get("seal"):
                                        taken_off.add(line[k]["seal"])        # told to STK as a person joining, or to be
                                if line.get("queued") and isinstance(line["queued"], dict):
                                    r = json.loads(line["queued"]["row"])
                                    if "conversation_id" in r:
                                        _finished["done"].add((r["conversation_id"], r["intent"]))
                                        _finished["seals"][(r["conversation_id"], r["intent"])] = line["queued"]["seal"]
                                if line.get("sig") and not line.get("cancelled"):
                                    r = json.loads(line["row"])
                                    if "conversation_id" in r:
                                        _finished["done"].add((r["conversation_id"], r["intent"]))
                                        _finished["seals"][(r["conversation_id"], r["intent"])] = line["receipt"]["seal"]
                            except Exception:
                                continue
                except OSError:
                    pass
                for x in [x for x, v in _finished["seals"].items() if v in taken_off]:
                    del _finished["seals"][x]
                    _finished["done"].discard(x)
        first = not _finished.get("queue_read")
        _finished["queue_read"] = True
    if ON_ROW is None and first:
        _reload_queue()
    with _lock:
        return _finished["done"]


def _reload_queue():
    """After a restart: the queued lines of today and yesterday with no signed or not_signed line yet go back in the queue,
    and their to_tell lines with no joined or not_told line of them yet are told."""
    waiting, gone, tells, told = {}, set(), {}, set()
    for d in (time.strftime("%Y-%m-%d", time.gmtime(time.time() - 86400)), _today()):
        try:
            with open(os.path.join(ROWS_DIR, d + ".jsonl"), encoding="utf-8") as f:
                for text in f:
                    try:
                        line = json.loads(text)
                    except Exception:
                        continue
                    if isinstance(line.get("queued"), dict):
                        waiting[line["queued"]["seal"]] = line["queued"]
                    elif line.get("receipt"):
                        gone.add(line["receipt"].get("seal"))
                    for k in ("not_signed", "dequeued", "joined"):
                        if isinstance(line.get(k), dict):
                            gone.add(line[k].get("seal"))
                    if isinstance(line.get("to_tell"), dict) and line["to_tell"].get("id"):
                        tells[line["to_tell"]["id"]] = line["to_tell"]
                    for k in ("joined", "not_told"):
                        if isinstance(line.get(k), dict) and line[k].get("of"):
                            told.add(line[k]["of"])
        except OSError:
            pass
    with _lock:
        for seal, q in waiting.items():
            if seal not in gone:
                _queue.setdefault(seal, q)
        for tid, t in tells.items():
            if tid not in told:
                _tells.setdefault(tid, t)
    _start_sender()
    _start_teller()


def seal_of(nonce: bytes, row_text: str) -> str:
    return hashlib.sha256(nonce + row_text.encode("utf-8")).hexdigest()


def ask(intent, trigger, conversation_id=None, **fields):
    intent = intent.strip().lower() if isinstance(intent, str) else intent      # " Order.Status " is order.status
    trigger = trigger.strip().lower() if isinstance(trigger, str) else trigger
    if not _rules:                            # the first ask of this process reads the rules first (up to 2 seconds),
        at = _rules_failed["at"]              # outside the 300 ms that STK's answer has
        if at is not None and time.monotonic() - at < RULES_RETRY:
            return "escalate"                 # just failed: not 2 seconds more for each ask while STK is away
        try:
            rules(timeout=2)
            _rules_failed["at"] = None
        except Exception:
            _rules_failed["at"] = time.monotonic()
            return "escalate"
    got, ready, decided, late = {}, threading.Event(), threading.Event(), [None, None]

    def answer(d):                            # the result, handed over before anything that may wait
        if "d" not in got:
            got["d"] = d
            ready.set()

    def work():
        try:
            _ask(intent, trigger, conversation_id, fields, answer, decided, late)
        except Exception:
            pass
        answer("escalate")

    threading.Thread(target=work, daemon=True).start()
    on_time = ready.wait(TIMEOUT)
    covered = not on_time and late[1] is not None and late[1]["ok"]()
    with _lock:
        if late[0] is None:                   # first to settle wins: the answer, the grant, or late
            late[0] = "answer" if on_time else ("grant" if covered else "late")
    decided.set()
    if late[0] == "grant":
        return "finish"
    return got.get("d", "escalate") if on_time else "escalate"


def _ask(intent, trigger, conversation_id, fields, answer, decided, late):
    r = rules()
    if decide(r["text"], intent, trigger) != "finish":
        answer("escalate")                    # STK is not called: nothing is sent, nothing is billed
        if not listed(r["text"], intent):     # on no list of the rules: a line here, for your own count; STK is not told
            _write({"not_listed": {"time_ms": int(time.time() * 1000), "intent": intent}})
        return
    cid = None if conversation_id is None else str(conversation_id)
    if cid is not None:
        while True:
            if (cid, intent) in _done_today():
                return answer("finish")       # got finish today: not asked again, not billed again
            with _lock:
                other = _asking.get((cid, intent))
                if other is None:
                    mine = _asking[(cid, intent)] = threading.Event()
                    break
            other.wait(15)                    # the same conversation and intent being asked now: its answer, not a second call
    try:
        _ask_stk(intent, trigger, cid, fields, r, answer, decided, late)
    finally:
        if cid is not None:
            with _lock:
                _asking.pop((cid, intent), None)
            mine.set()


def _ask_stk(intent, trigger, cid, fields, r, answer, decided, late):
    row = dict(fields, intent=intent, trigger=trigger, **({} if cid is None else {"conversation_id": cid}))
    text = row_text(row)
    nonce = secrets.token_bytes(32)
    seal = seal_of(nonce, text)
    recorded = _now_ms()
    with _lock:
        g = dict(_grant) if _grant.get("g") else None
    late[1] = {"ok": lambda: _grant_ok(r["version"])}
    try:
        try:
            a = _http("POST", "/v1/ask", {"seal": seal, "recorded_ms": recorded})
        except urllib.error.HTTPError as e:   # this machine's clock is more than a minute from STK's: STK's, then once again
            if e.code != 422 or not e.headers.get("X-STK-Time-Ms"):
                raise
            _clock["offset"] = int(e.headers["X-STK-Time-Ms"]) - int(time.time() * 1000)
            recorded = _now_ms()
            a = _http("POST", "/v1/ask", {"seal": seal, "recorded_ms": recorded})
    except Exception as e:
        reached = isinstance(e, urllib.error.HTTPError) and e.code < 500 and e.code not in (408, 429)   # STK busy: not reached
        with _lock:
            if late[0] is None:
                late[0] = "grant" if not reached and g and g["g"]["rule_version"] == r["version"] \
                    and time.monotonic() < g["until"] and len(_queue) < QUEUE_MAX else "error"
            how = late[0]
            if how == "grant" and not g:
                g = dict(_grant) if _grant.get("g") else None
        if how == "grant" and g:                    # STK not reached, the grant holds: finish now, the seal waits in the queue
            _enqueue(cid, intent, text, nonce, seal, recorded, g)
            return answer("finish")
        try:                                  # it may have been signed and counted: taken off. Once only: STK most often
            _post_joined("no answer from STK", seal)    # never had it, and a join lowers the day's bill
        except Exception:
            pass
        raise
    _keep_grant(a)
    _learn_receipt_clock(a)
    if not a.get("sig"):
        answer("escalate")                    # not signed: no permission, not billed
        decided.wait()
        if late[0] == "grant":                # ask() had already returned finish under the grant: kept, so it is known
            _write({"not_signed": {"seal": seal, "recorded_ms": recorded, "why": a.get("not_signed") or "STK did not sign it"}})
        return
    line = {"row": text, "nonce": nonce.hex(), "receipt": a["receipt"], "sig": a["sig"]}
    result = "finish"
    if a["rule_version"] != r["version"] and late[0] != "grant":     # newer rules: read them, apply them again
        try:
            r = rules(fresh=True)
            if decide(r["text"], intent, trigger) != "finish":
                result, line["cancelled"] = "escalate", "the rules of " + a["rule_version"][:12] + " say escalate"
        except Exception:                     # the newer rules could not be read: escalate, and taken off
            result, line["cancelled"] = "escalate", "the rules of " + a["rule_version"][:12] + " could not be read"
    if line.get("cancelled"):
        _tell_joined(line)
    try:
        _write(line)                          # kept before the answer: a process stopped right after it still has it
    except Exception:
        if not line.get("cancelled"):         # not kept: never a permission you cannot prove; taken off, escalate
            line["cancelled"] = "the line could not be kept"
            _tell_joined(line)
        raise
    if not line.get("cancelled") and cid is not None:
        with _lock:
            if _finished["day"] == _today():
                _finished["done"].add((cid, intent))
                _finished["seals"][(cid, intent)] = seal
    answer(result)
    decided.wait()                            # ask() has returned, on time or not
    if result == "finish" and late[0] == "late":   # the answer came too late: your code has handed it to a person
        with _lock:
            _finished["done"].discard((cid, intent))
            _finished["seals"].pop((cid, intent), None)
        _tell("the answer came after ask() returned", seal)    # its joined line takes it off your count too
    _save_key(line["receipt"]["kid"])


def _learn_receipt_clock(a):
    try:
        diff = a["receipt"]["time_ms"] - time.time() * 1000
        _clock["offset"] = int(diff) if abs(diff) > 30000 else 0
    except Exception:
        pass


def _enqueue(cid, intent, text, nonce, seal, recorded, g):
    q = {"row": text, "nonce": nonce.hex(), "seal": seal, "recorded_ms": recorded, "grant": g["g"], "grant_sig": g["sig"]}
    _write({"queued": q})                     # kept before the answer, as every permission
    with _lock:
        _queue[seal] = q
        if cid is not None and _finished["day"] == _today():
            _finished["done"].add((cid, intent))
            _finished["seals"][(cid, intent)] = seal
    _start_sender()


def _start_sender():
    with _lock:
        if _sender["on"] or not _queue:
            return
        _sender["on"] = True
    threading.Thread(target=_send_queue, daemon=True).start()


def _send_queue():
    """The queued seals, sent in the order recorded, as soon as STK answers. Each signed one becomes an ordinary line
    (from_queue: true), its receipt with both times. One STK refuses (its grant did not hold): a not_signed line."""
    try:
        while True:
            with _lock:
                if not _queue:
                    return
                seal, q = next(iter(_queue.items()))
            try:
                a = _http("POST", "/v1/ask", {"seal": seal, "recorded_ms": q["recorded_ms"], "grant": q["grant"], "grant_sig": q["grant_sig"]})
            except urllib.error.HTTPError as e:
                if e.code >= 500 or e.code in (408, 429):
                    time.sleep(QUEUE_RETRY); continue
                _write({"not_signed": {"seal": seal, "recorded_ms": q["recorded_ms"], "why": "STK refused it: " + str(e.code)}})
                with _lock:
                    _queue.pop(seal, None)
                continue
            except Exception:
                time.sleep(QUEUE_RETRY); continue
            _keep_grant(a)
            if not a.get("sig"):
                _write({"not_signed": {"seal": seal, "recorded_ms": q["recorded_ms"], "why": a.get("not_signed") or "STK did not sign it"}})
            else:
                _write({"row": q["row"], "nonce": q["nonce"], "receipt": a["receipt"], "sig": a["sig"], "from_queue": True})
                _save_key(a["receipt"]["kid"])
            with _lock:
                _queue.pop(seal, None)
    finally:
        with _lock:
            _sender["on"] = False
        if _queue:
            _start_sender()


def flush(timeout=30):
    """Waits until the queue is empty or timeout seconds pass: True when empty. Call it before a process ends."""
    _start_sender()
    end = time.monotonic() + timeout
    while time.monotonic() < end:
        with _lock:
            if not _queue:
                return True
        time.sleep(0.05)
    return False


def _save_key(kid):
    """The public key of a receipt's kid, the first time this file sees it today: kept with the lines, so they can be
    checked with nothing of STK running (stk_verify.py --from-file)."""
    _done_today()
    with _lock:
        if kid in _finished["kids"]:
            return
        _finished["kids"].add(kid)
    try:
        k = _http("GET", "/v1/rules?keys=1&kid=" + kid, key=False)["keys"]
        if k:
            _write({"key": k[0]})
    except Exception:
        with _lock:
            _finished["kids"].discard(kid)


def _tell_joined(line):
    if not _tell(line["cancelled"], line.get("receipt", {}).get("seal")):   # a person has it: taken off its day's bill
        line["cancelled"] += "; STK is told when it answers"


def _post_joined(why, seal=None, of=None):
    """POST /v1/joined (with the permission's seal when known: it counts for that permission's day), and a line for
    it: your count of people joining is your joined lines."""
    a = _http("POST", "/v1/joined", {"seal": seal} if seal else {})
    _joined_line(a, why, seal, of)


def _joined_line(a, why, seal, of=None):
    j = {"time_ms": int(time.time() * 1000), "day": a.get("day"), "seal": seal, "why": why}
    if of:
        j["of"] = of                          # the to_tell line it was kept as
    try:
        _write({"joined": j})
    except Exception:
        pass                                  # STK was told; only your ON_ROW raised


def _tell(why, seal=None):
    """STK told a person joined, now: True. Not reached: kept as a to_tell line and told as soon as STK answers
    (False). Never raises."""
    try:
        _post_joined(why, seal)               # a line it cannot keep does not raise: STK is told once only
        return True
    except Exception:
        pass
    t = {"id": secrets.token_hex(8), "time_ms": int(time.time() * 1000), "seal": seal, "why": why}
    try:
        _write({"to_tell": t})
    except Exception:
        pass                                  # your ON_ROW raised: kept while this process runs
    with _lock:
        _tells[t["id"]] = t
    _start_teller()
    return False


def _start_teller():
    with _lock:
        if _teller["on"] or not _tells:
            return
        _teller["on"] = True
    threading.Thread(target=_send_tells, daemon=True).start()


def _send_tells():
    """Each person joining STK could not be told, in the order kept, as soon as STK answers: a joined line with of."""
    try:
        while True:
            with _lock:
                if not _tells:
                    return
                tid, t = next(iter(_tells.items()))
            try:
                _post_joined(t["why"], t.get("seal"), tid)
            except urllib.error.HTTPError as e:
                if e.code >= 500 or e.code in (408, 429):
                    time.sleep(QUEUE_RETRY); continue
                try:                          # STK refused it (a key stopped, for one): not told, and said so
                    _write({"not_told": {"time_ms": int(time.time() * 1000), "seal": t.get("seal"), "of": tid, "why": "STK refused it: " + str(e.code)}})
                except Exception:
                    pass
            except Exception:
                time.sleep(QUEUE_RETRY); continue
            with _lock:
                _tells.pop(tid, None)
    finally:
        with _lock:
            _teller["on"] = False
        if _tells:
            _start_teller()


def joined(conversation_id=None):
    """A person joined a conversation: STK is told, once for each finish this file knows the conversation got today
    (with its seal), or once without one. It counts for the day of the finish, or for today (UTC). Called again the
    same day for the same conversation with no finish of it since: STK is not told again. It never raises: STK not
    reached, it is told as soon as STK answers (a to_tell line until then). True, or False if your ON_ROW raised."""
    try:
        return _joined(conversation_id)
    except Exception:
        return False


def _joined(conversation_id):
    cid = None if conversation_id is None else str(conversation_id)
    seals = [None]
    if cid is not None:
        done = _done_today()
        with _lock:
            told = cid in _finished.setdefault("told", set())
            gone = sorted(x for x in done if x[0] == cid)
            seals = [_finished["seals"].get(x) for x in gone]
            if not gone and time.time() % 86400 < GRACE:
                seals = [s for x, s in sorted(_finished["yesterday"].items()) if x[0] == cid]
            if not seals and told:
                return True                   # told already today, and no finish of it since: not told again
            seals = seals or [None]
    for s in seals:
        with _lock:
            waiting = _queue.pop(s, None) if s is not None else None
        if waiting is not None:               # still in the queue: never sent, never billed
            _write({"dequeued": {"time_ms": int(time.time() * 1000), "seal": s, "why": "joined(" + ("" if cid is None else cid) + ") before STK signed it"}})
        else:
            _tell("joined(" + ("" if cid is None else cid) + ")", s)    # STK not reached: told as soon as it answers
        with _lock:                                                      # told: not told again for it
            for book in (_finished["seals"], _finished["yesterday"]):
                for x in [x for x, v in book.items() if v == s and s is not None]:
                    del book[x]
                    _finished["done"].discard(x)
        if s is None and cid is not None:
            with _lock:
                _finished["done"] -= {x for x in _finished["done"] if x[0] == cid}
    if cid is not None:
        with _lock:
            _finished.setdefault("told", set()).add(cid)
    return True


if __name__ == "__main__":
    if len(sys.argv) < 2:
        sys.exit("python3 stk.py <intent> [trigger]   (decides from STK's public rules; sends nothing)")
    r = rules()
    print(decide(r["text"], sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else "unknown"), "(rules " + r["version"][:12] + ")")
