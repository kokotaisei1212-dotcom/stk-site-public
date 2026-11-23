// STK: ask before your AI hands a conversation to a person. https://stk-evidence.com/docs
//
//   import { ask, joined } from "./stk.mjs";
//   if (await ask(intent, trigger, { conversationId }) === "finish") { /* your AI goes on */ } else { /* hand it to a person */ }
//   await joined(conversationId);   // a person joined a conversation that got finish: taken off its day's bill
//
// trigger: a trigger of the rules' Triggers list (https://stk-evidence.com/rules-full#triggers) that happened in the
// conversation: customer_asked, distressed, angry, bereavement, threat, legal_claim; or unknown when none of them
// happened (the only one the rules can answer finish to).
// This file decides, here, on your side, from STK's public rules (GET /v1/rules, the same for every company, signed by
// STK). STK receives nothing of the conversation. Only on finish does it call STK, and it sends the seal and the time it recorded the action:
// SHA-256 of 32 random bytes and your row (intent, trigger and any fields you give in the third argument). The row and
// the random bytes stay here. STK signs the seal with the time and the rules version: that is the permission, and each
// one is billed. Unpaid 60 days after a due date, or STK without a published key: no signature, and ask() escalates.
// Each permission is one JSON line in ROWS_DIR/<day>.jsonl (by default ./stk-rows, or STK_ROWS_DIR), kept before ask()
// returns, or given to setOnRow(fn) for your own store; if the folder cannot be written, the line goes to standard
// output; if your function throws, the permission is told to STK as a person joining and ask() escalates. Check them:
// stk_verify.py. An intent on no list of the rules leaves a not_listed line there, for your own count; STK is not told.
// When STK's answer says a newer version of the rules, this file reads them again and applies them again; if they now
// say escalate, it escalates and tells STK a person has it, so it is not billed. The same conversation and intent that
// got finish today (UTC) gets finish again without calling STK. Without an answer within 300 ms, or on any error,
// ask() escalates; a late permission is told to STK as a person joining, so it is not billed.
// Each answer of STK's also brings a grant, signed by STK, for this account and this version of the rules, for 1 hour
// (never past the next April 15 or October 15, 00:00 UTC, the only days a restriction takes effect, nor past the moment
// the account would be unpaid 60 days). It is kept in the rows folder (a grant line, at most every 5 minutes), with the
// rules it names, so a process started again while STK cannot be reached finishes under it too (not with onRow).
// If STK cannot be reached (no answer within 300 ms, or an error reaching it) while the last grant holds, the rules here
// say finish and the queue is not full, ask() returns "finish" and the seal waits in a queue, kept as a queued line; it
// is sent as soon as STK answers again, and STK signs it as any seal. The grant gone, or queueMax seals waiting:
// "escalate", as before. A receipt has two times: recorded_ms, when this file recorded the action (your claim), and
// time_ms, when STK signed (what STK attests). They are the same moment unless the seal waited in the queue.
// STK's own trouble never reaches your code as an error: ask() resolves to finish or escalate, and joined() resolves. A
// starting STK server, or one that cannot read the unpaid state from Stripe, answers 503, and a 429 is the same: STK not
// reached, so the grant holds as above. A person joining that STK cannot be told is kept (a to_tell line) and told as
// soon as STK answers, also after a restart; told after 00:10 UTC the day after the finish, it stays billed. After the
// rules could not be read, ask() escalates at once for rulesRetry ms instead of waiting 2 seconds each time.
// Try it without a key: node stk.mjs conversation.order.status unknown   (it reads the public rules; it sends nothing)
// Node 18 or later, nothing to install.
import { createHash, randomBytes } from "node:crypto";
import { appendFile, mkdir, readFile } from "node:fs/promises";
import { join } from "node:path";
import { pathToFileURL } from "node:url";
export const config = {
  key: (typeof process !== "undefined" && process.env && process.env.STK_KEY) || "",   // your key, from the environment (STK_KEY): the test key first, the live key when you go live
  api: process.env.STK_API || "https://api.stk-evidence.com",
  timeout: 300,
  rowsDir: process.env.STK_ROWS_DIR || "stk-rows",
  onRow: null,           // or a function(line): each line, for your own store
  queueMax: 10000,       // seals waiting for STK at most; past it, "escalate"
  queueRetry: 5000,      // ms between tries to send the queue, and a person joining STK could not be told yet
  rulesRetry: 10000,     // ms after the rules could not be read in which ask() escalates without trying again
};
const tells = new Map(); // id -> a person joining that STK could not be told yet (a to_tell line)
let telling = false;
let rulesFailed = null;  // when the rules last could not be read (performance.now())
const saved = { read: false, rules: new Map(), grantAt: null, rulesDay: null };   // read back from the rows folder
const GRANT_SAVE = 300000;   // ms between grant lines kept in the rows folder
const busy = (st) => st === undefined || st >= 500 || st === 408 || st === 429;   // STK not reached, or busy: try again
let grant = null;        // the last grant: g, sig, until (performance.now())
const queue = new Map(); // seal -> its queued line, waiting for STK; in the order recorded
let offset = 0;          // ms to add to this machine's clock when STK said it is more than a minute off
let sending = false;
const nowMs = () => Date.now() + offset;
const grantOk = (version) => !!grant && grant.g.rule_version === version && performance.now() < grant.until && queue.size < config.queueMax;
function keepGrant(a) {
  if (a && a.grant && a.grant_sig) {
    const prev = grant;
    grant = { g: a.grant, sig: a.grant_sig, until: performance.now() + (a.grant.expires_ms - a.grant.issued_ms) };
    if (!config.onRow && (saved.grantAt === null || performance.now() - saved.grantAt >= GRANT_SAVE || !prev || prev.g.rule_version !== a.grant.rule_version)) {
      saved.grantAt = performance.now();
      const g = { g: a.grant, sig: a.grant_sig };
      (async () => {
        if (saved.rulesDay !== today() && current) { await write({ rules: current }); saved.rulesDay = today(); }   // today's file has the rules a grant names
        await write({ grant: g });                                                                           // read back after a restart
      })().catch(() => {});
    }
  }
  if (a && a.receipt) { const d = a.receipt.time_ms - Date.now(); offset = Math.abs(d) > 30000 ? d : 0; }
}
export function setOnRow(fn) { config.onRow = fn; }
let current = null;      // the signed rules in use
const done = { day: null, set: new Set(), kids: new Set(), seals: new Map(), yesterday: new Map(), told: new Set() };
const GRACE = 600;   // seconds after midnight (UTC) in which STK counts a seal of the day before for its day
const today = () => new Date(Date.now()).toISOString().slice(0, 10);

// An intent's full name, with its domain (conversation.claim.status), is read as the name listed (claim.status).
function named(intent, sets) {
  const has = (x) => sets.some((s) => s.has(x));
  return typeof intent === "string" && intent.startsWith("conversation.") && has(intent.slice(13)) ? intent.slice(13) : intent;
}

export function decide(text, intent, trigger) {
  const lst = (name) => {
    const m = text.match(new RegExp("^" + name + " \\((\\d+)\\): (.*)$", "m"));
    const items = m[2] === "none" ? [] : m[2].split(",").map((x) => x.trim().split(" (closed")[0]);
    if (items.length !== Number(m[1])) throw new Error("the rules text does not read as STK's");
    return new Set(items);
  };
  const never = lst("Never"), permitted = lst("Permitted"), closed = lst("Closed");
  intent = named(intent, [never, permitted, closed]);
  if (trigger !== "unknown") return "escalate";
  if (never.has(intent)) return "escalate";
  if (!never.has(intent) && !permitted.has(intent) && !closed.has(intent)) return "escalate";
  if (closed.has(intent)) return "escalate";
  return "finish";
}

// ---- jurisdictions (from Rule 9) and the days laws apply from (from Rule 10) ----
const H9 = "The jurisdictions of the laws beside each intent on the Never list";
const H10 = "Where each law beside an intent on the Never list applies, and from when";

// The codes given, as the rules read them (UK is GB), sorted; null when none is given or one is not a code.
export function jurisdictions(where) {
  if (typeof where === "string") where = [where];
  if (!Array.isArray(where) || where.length === 0) return null;
  const out = new Set();
  for (let c of where) {
    if (typeof c !== "string") return null;
    c = c.trim().toUpperCase();
    if (c === "UK" || c.startsWith("UK-")) c = "GB" + c.slice(2);
    if (!/^[A-Z]{2}(-[A-Z0-9]{1,3})?$/.test(c)) return null;
    out.add(c);
  }
  return [...out].sort();
}

function items(text, head) {
  const esc = head.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
  const m = text.match(new RegExp("^" + esc + "[^\\n]*\\n((?:- [^\\n]*\\n?)*)", "m"));
  return m === null ? null : m[1].split("\n").filter((x) => x !== "").map((x) => x.slice(2));
}

const pair = (x) => { const k = x.indexOf(": "); return [x.slice(0, k), x.slice(k + 2)]; };

function subjectsOf(text) {
  const subject = new Map();
  for (const x of items(text, "The subject of each intent:") || []) { const [sj, names] = pair(x); for (const n of names.split(", ")) subject.set(n, sj); }
  return subject;
}

// { answer, status } on a day (YYYY-MM-DD, UTC; today when omitted). status: null when no jurisdiction is given; else "read",
// "none found" or "not checked". Only "read" can answer less strictly than with none given. Rules older than Rule 9 (or Rule 9's,
// which wrote no days): every law applies from the day it is cited.
export function decideAt(text, intent, trigger, where = null, day = null) {
  const strict = decide(text, intent, trigger);
  if (where !== null && where !== undefined && intent !== "other" && !listed(text, intent))
    return { answer: strict, status: "not published" };   // an action these rules do not publish: a person, and STK claims nothing of it
  day = day || today();
  const codes = jurisdictions(where);
  if (items(text, H10) === null) {                       // Rule 9 or older
    if (where === null || where === undefined) return { answer: strict, status: null };
    const r = decide9(text, intent, trigger, codes);
    return { answer: r.answer, status: r.read ? "read" : "not checked" };
  }
  const beside = new Map();
  for (const x of items(text, H10)) {
    const [k, v] = pair(x);
    beside.set(k, new Map(v.split(", ").map((g) => g.includes(" from ") ? g.split(" from ") : [g, null])));
  }
  const subject = subjectsOf(text);
  const i = typeof intent === "string" && intent.startsWith("conversation.") && subject.has(intent.slice(13)) ? intent.slice(13) : intent;
  const applies = (f) => f === null || f <= day;
  let dated = strict;
  if (!(strict === "finish" || trigger !== "unknown" || typeof i !== "string" || !beside.has(i)))
    dated = [...beside.get(i).values()].some(applies) ? "escalate" : "finish";
  if (where === null || where === undefined) return { answer: dated, status: null };
  if (codes === null) return { answer: dated, status: "not checked" };
  const parts = new Map(), members = new Map();
  for (const [head, into] of [["Parts, whose laws apply wherever their country's code is given:", parts],
                              ["Members, whose code brings in the laws of what they are members of:", members]])
    for (const x of items(text, head) || []) { const [k, v] = pair(x); into.set(k, v.split(", ")); }
  const up = (c) => [parts, members].flatMap((g) => [...g].filter(([, ms]) => ms.includes(c)).map(([k]) => k));
  const near = (c) => new Set([c, ...up(c), ...(parts.get(c) || [])]);
  const checked = new Map();
  for (const x of items(text, "Checked (") || []) {
    const m = x.match(/^([a-z]+) in ([A-Z0-9, -]+): (read|none found): /);
    if (m) for (const c of m[2].split(", ")) checked.set(m[1] + "|" + c, m[3]);
  }
  const sj = typeof i === "string" ? subject.get(i) : undefined;
  const marks = sj === undefined ? ["not checked"] : codes.flatMap((code) => [...near(code)].map((c) => checked.get(sj + "|" + c) || "not checked"));
  const status = marks.includes("not checked") ? "not checked" : (marks.includes("read") ? "read" : "none found");
  if (status !== "read") return { answer: dated, status };
  if (dated === "finish" || strict === "finish" || trigger !== "unknown" || !beside.has(i)) return { answer: dated, status };
  const named = codes.some((c) => [...beside.get(i)].some(([g, f]) => applies(f) && near(c).has(g)));
  return { answer: named ? "escalate" : "finish", status };
}

function decide9(text, intent, trigger, codes) {         // Rule 9's reading
  const strict = decide(text, intent, trigger);
  const laws = items(text, H9), subjects = items(text, "The subject of each intent:"), read = items(text, "Read (");
  if (codes === null || laws === null || subjects === null || read === null) return { answer: strict, read: false };
  const subject = subjectsOf(text);
  const i = typeof intent === "string" && intent.startsWith("conversation.") && subject.has(intent.slice(13)) ? intent.slice(13) : intent;
  const sj = typeof i === "string" ? subject.get(i) : undefined;
  const done = new Map();
  for (const x of read) {
    const m = x.match(/^([a-z]+) in ([A-Z0-9, -]+): /);
    if (m) { if (!done.has(m[1])) done.set(m[1], new Set()); for (const c of m[2].split(", ")) done.get(m[1]).add(c); }
  }
  if (sj === undefined || !codes.every((c) => done.has(sj) && done.get(sj).has(c))) return { answer: strict, read: false };
  if (strict === "finish" || trigger !== "unknown") return { answer: strict, read: true };
  const beside = new Map(laws.map((x) => { const [k, v] = pair(x); return [k, v.split(", ")]; }));
  if (!beside.has(i)) return { answer: strict, read: true };
  const named = codes.some((c) => beside.get(i).some((g) => c === g || c.split("-")[0] === g || g.split("-")[0] === c));
  return { answer: named ? "escalate" : "finish", read: true };
}

// Rule 9's call, kept: { answer, read } today.
export function decideWhere(text, intent, trigger, where) {
  const r = decideAt(text, intent, trigger, where);
  return { answer: r.answer, read: r.status === "read" };
}

const judge = (text, intent, trigger, where) => decideAt(text, intent, trigger, where).answer;

export function listed(text, intent) {   // the intent is on one of the rules' lists (Never, Permitted, Closed)
  for (const name of ["Never", "Permitted", "Closed"]) {
    const m = text.match(new RegExp("^" + name + " \\((\\d+)\\): (.*)$", "m"));
    const items = m[2] === "none" ? [] : m[2].split(",").map((x) => x.trim().split(" (closed")[0]);
    if (items.includes(intent) || (typeof intent === "string" && intent.startsWith("conversation.") && items.includes(intent.slice(13)))) return true;
  }
  return false;
}

async function http(method, path, body, key = true, ms = 10000) {
  const headers = { "Content-Type": "application/json", "User-Agent": "stk.mjs" };
  if (key) headers["X-STK-Key"] = config.key;
  const r = await fetch(config.api + path, { method, headers, body: body === undefined ? undefined : JSON.stringify(body),
    signal: AbortSignal.timeout(ms) });
  if (!r.ok) { const e = new Error(String(r.status)); e.status = r.status; e.headers = r.headers; throw e; }
  return r.json();
}

async function write(line) {
  if (config.onRow) return config.onRow(line);
  const text = JSON.stringify(line);
  try {
    await mkdir(config.rowsDir, { recursive: true });
    await appendFile(join(config.rowsDir, today() + ".jsonl"), text + "\n");
  } catch { process.stdout.write(text + "\n"); }
}

export async function rules(fresh = false, ms = 10000) {
  if (current && !fresh) return current;
  const r = await http("GET", "/v1/rules", undefined, false, ms);
  decide(r.text, "", "unknown");
  const isNew = !current || current.version !== r.version;
  current = r;
  if (isNew) { await write({ rules: r }); saved.rulesDay = today(); }
  return r;
}

let loading = null;   // today's file being read: every caller waits for the same read

async function doneToday() {
  const d = today();
  if (done.day === d) return done.set;
  if (!loading || loading.day !== d) {
    loading = { day: d, p: (async () => {
      const set = new Set(), kids = new Set(), seals = new Map(), takenOff = new Set();
      if (!config.onRow) {
        try {
          for (const t of (await readFile(join(config.rowsDir, d + ".jsonl"), "utf8")).split("\n")) {
            try {
              const l = JSON.parse(t);
              if (l.key) kids.add(l.key.kid);
              for (const k of ["joined", "to_tell"]) if (l[k] && l[k].seal) takenOff.add(l[k].seal);   // told to STK as a person joining, or to be
              if (l.queued && l.queued.row) { const r = JSON.parse(l.queued.row); if ("conversation_id" in r) { set.add(r.conversation_id + "\u0000" + r.intent); seals.set(r.conversation_id + "\u0000" + r.intent, l.queued.seal); } }
              if (l.sig && !l.cancelled) { const r = JSON.parse(l.row); if ("conversation_id" in r) { set.add(r.conversation_id + "\u0000" + r.intent); seals.set(r.conversation_id + "\u0000" + r.intent, l.receipt.seal); } }
            } catch {}
          }
        } catch {}
      }
      for (const [x, v] of [...seals]) if (takenOff.has(v)) { seals.delete(x); set.delete(x); }
      if (done.day === null && !config.onRow) await reloadQueue();
      if (done.day !== d) { if (done.day !== null) done.yesterday = done.seals; done.day = d; done.set = set; done.kids = kids; done.seals = seals; done.told = new Set(); }   // set only once the file is read
    })() };
  }
  await loading.p;
  return done.set;
}

const asking = new Map();   // conversation and intent being asked now: one call to STK for them

const byCodePoint = (a, b) => {   // as Python sorts text: by code point, not by UTF-16 unit
  const x = [...a], y = [...b];
  for (let i = 0; i < Math.min(x.length, y.length); i++) { const d = x[i].codePointAt(0) - y[i].codePointAt(0); if (d) return d; }
  return x.length - y.length;
};

// The row as text, one way only, the same in stk.py and stk.mjs: keys sorted by code point, no spaces, Unicode as it
// is, numbers as JavaScript writes them, NaN and infinities as null. Its bytes are what is sealed.
export function rowText(v) {
  if (v === null || v === undefined) return "null";
  if (typeof v === "boolean") return v ? "true" : "false";
  if (typeof v === "number") return Number.isFinite(v) ? JSON.stringify(v) : "null";
  if (typeof v === "string") return JSON.stringify(v);
  if (Array.isArray(v)) return "[" + v.map((x) => (typeof x === "function" ? "null" : rowText(x))).join(",") + "]";
  if (typeof v === "object") {
    if (typeof v.toJSON === "function") return rowText(v.toJSON());
    const ks = Object.keys(v).filter((k) => v[k] !== undefined && typeof v[k] !== "function").sort(byCodePoint);
    return "{" + ks.map((k) => JSON.stringify(k) + ":" + rowText(v[k])).join(",") + "}";
  }
  throw new TypeError("a row holds text, numbers, true, false, null, lists and objects only");
}

export const sealOf = (nonce, rowText) => createHash("sha256").update(Buffer.concat([nonce, Buffer.from(rowText, "utf8")])).digest("hex");

export async function ask(intent, trigger, { conversationId, ...fields } = {}) {
  return askAny(intent, trigger, conversationId, fields, null);
}

// ask(), for the jurisdictions whose laws apply to this decision (from Rule 9): a code or a list of codes, ISO 3166-1 (US, GB),
// ISO 3166-2 (US-WA) or EU; UK is read as GB. { answer: "finish" or "escalate", read: true or false, status: "read", "none found" or
// "not checked" }. Only "read" (a law that names a person was found) answers by those jurisdictions' laws; "none found" and
// "not checked" answer as ask(), the strictest. The codes are kept in the row, as "jurisdiction"; STK still receives only the seal.
export async function askWhere(intent, trigger, jurisdiction, { conversationId, ...fields } = {}) {
  const where = jurisdictions(jurisdiction);
  const answer = await askAny(intent, trigger, conversationId, fields, where);
  let status = "not checked";
  try {
    if (where !== null && current) status = decideAt(current.text, typeof intent === "string" ? intent.trim().toLowerCase() : intent,
      typeof trigger === "string" ? trigger.trim().toLowerCase() : trigger, where).status;
  } catch {}
  return { answer, read: status === "read", status };
}

async function askAny(intent, trigger, conversationId, fields, where) {
  if (typeof intent === "string") intent = intent.trim().toLowerCase();   // " Order.Status " is order.status
  if (typeof trigger === "string") trigger = trigger.trim().toLowerCase();
  if (!current) {   // the first ask of this process reads the rules first (up to 2 seconds), outside STK's 300 ms
    try { await readSaved(); } catch {}
    if (rulesFailed !== null && performance.now() - rulesFailed < config.rulesRetry) { if (!rulesUnderGrant()) return "escalate"; }   // just failed: not 2 s more each ask
    else {
      try { await rules(false, 2000); rulesFailed = null; }
      catch { rulesFailed = performance.now(); if (!rulesUnderGrant()) return "escalate"; }   // a restart while STK is away: the kept grant and its rules
    }
  }
  const state = { late: false, how: null, covered: () => false, settle: null, answer: null };
  const settled = new Promise((r) => (state.settle = r));
  const answered = new Promise((r) => (state.answer = r));   // the result, handed over before anything that may wait
  run(intent, trigger, conversationId, fields, state, settled, where).catch(() => {}).finally(() => state.answer("escalate"));
  const timer = new Promise((r) => setTimeout(() => r("late"), config.timeout));
  const first = await Promise.race([answered, timer]);
  if (state.how === null) state.how = first !== "late" ? "answer" : (state.covered() ? "grant" : "late");   // first to settle wins
  state.late = state.how === "late";
  state.settle();
  if (state.how === "grant") return "finish";
  return state.late ? "escalate" : first;
}

async function run(intent, trigger, conversationId, fields, state, settled, where = null) {
  let r = await rules();
  if (judge(r.text, intent, trigger, where) !== "finish") {
    state.answer("escalate");                                // STK is not called
    if (!listed(r.text, intent)) await write({ not_listed: { time_ms: Date.now(), intent } });   // for your own count; STK is not told
    return;
  }
  const cid = conversationId === undefined || conversationId === null ? null : String(conversationId);
  const k = cid === null ? null : cid + "\u0000" + intent;
  if (k !== null) {
    for (;;) {
      if ((await doneToday()).has(k)) return state.answer("finish");   // got finish today: not asked again, not billed again
      const other = asking.get(k);
      if (!other) break;
      await other;                                           // being asked now: its answer, not a second call
    }
    let release;
    asking.set(k, new Promise((r) => (release = r)));
    try { return await ask1(intent, trigger, cid, fields, state, settled, r, where); }
    finally { asking.delete(k); release(); }
  }
  return ask1(intent, trigger, cid, fields, state, settled, r, where);
}

async function ask1(intent, trigger, cid, fields, state, settled, r, where = null) {
  const row = { ...fields, intent, trigger };
  if (cid !== null) row.conversation_id = cid;
  if (where !== null) row.jurisdiction = where;            // askWhere: the codes given, sealed with the row
  const text = rowText(row);
  const nonce = randomBytes(32);
  const seal = sealOf(nonce, text);
  let recorded = nowMs();
  const g = grant;
  state.covered = () => grantOk(r.version);
  let a;
  try {
    try { a = await http("POST", "/v1/ask", { seal, recorded_ms: recorded }); }
    catch (e) {                                              // this machine's clock is more than a minute from STK's: STK's, then once again
      if (e.status !== 422 || !e.headers || !e.headers.get("x-stk-time-ms")) throw e;
      offset = Number(e.headers.get("x-stk-time-ms")) - Date.now(); recorded = nowMs();
      a = await http("POST", "/v1/ask", { seal, recorded_ms: recorded });
    }
  } catch (e) {
    const reached = !busy(e.status);
    if (state.how === null) state.how = !reached && g && g.g.rule_version === r.version && performance.now() < g.until && queue.size < config.queueMax ? "grant" : "error";
    if (state.how === "grant" && (g || grant)) {             // STK not reached, the grant holds: finish now, the seal waits in the queue
      await enqueue(cid, intent, text, nonce, seal, recorded, g || grant);
      return state.answer("finish");
    }
    try { await postJoined("no answer from STK", seal); } catch {} throw e;   // it may have been counted: taken off; once only (STK most often never had it, and a join lowers the bill)
  }
  keepGrant(a);
  if (!a.sig) {
    state.answer("escalate");                                // not signed: no permission, not billed
    await settled;
    if (state.how === "grant") await write({ not_signed: { seal, recorded_ms: recorded, why: a.not_signed || "STK did not sign it" } });   // ask() had returned finish under the grant
    return;
  }
  const line = { row: text, nonce: nonce.toString("hex"), receipt: a.receipt, sig: a.sig };
  let result = "finish";
  if (a.rule_version !== r.version && state.how !== "grant") {
    try {
      r = await rules(true);
      if (judge(r.text, intent, trigger, where) !== "finish") { result = "escalate"; line.cancelled = "the rules of " + a.rule_version.slice(0, 12) + " say escalate"; }
    } catch { result = "escalate"; line.cancelled = "the rules of " + a.rule_version.slice(0, 12) + " could not be read"; }   // taken off
  }
  const key = cid === null ? null : cid + "\u0000" + intent;
  const tellIt = async () => { if (!(await tell(line.cancelled, seal))) line.cancelled += "; STK is told when it answers"; };
  if (line.cancelled) await tellIt();
  try { await write(line); }                                 // kept before the answer: a process stopped right after it still has it
  catch (e) {                                                // not kept: never a permission you cannot prove; taken off, escalate
    if (!line.cancelled) { line.cancelled = "the line could not be kept"; await tellIt(); }
    throw e;
  }
  if (!line.cancelled && key !== null && done.day === today()) { done.set.add(key); done.seals.set(key, seal); }
  state.answer(result);
  await settled;                                             // ask() has returned, on time or not
  if (result === "finish" && state.late) {                   // too late: your code has handed it to a person
    if (key !== null) { done.set.delete(key); done.seals.delete(key); }
    await tell("the answer came after ask() returned", seal);   // its joined line takes it off your count too
  }
  await saveKey(line.receipt.kid);
}

async function enqueue(cid, intent, text, nonce, seal, recorded, g) {
  const q = { row: text, nonce: nonce.toString("hex"), seal, recorded_ms: recorded, grant: g.g, grant_sig: g.sig };
  await write({ queued: q });                                // kept before the answer, as every permission
  queue.set(seal, q);
  const key = cid === null ? null : cid + "\u0000" + intent;
  if (key !== null && done.day === today()) { done.set.add(key); done.seals.set(key, seal); }
  startSender();
}

function startSender() {
  if (sending || !queue.size) return;
  sending = true;
  sendQueue().finally(() => { sending = false; if (queue.size) setTimeout(startSender, config.queueRetry).unref?.(); });
}

// The queued seals, sent in the order recorded, as soon as STK answers. Each signed one becomes an ordinary line
// (from_queue: true), its receipt with both times. One STK refuses (its grant did not hold): a not_signed line.
async function sendQueue() {
  while (queue.size) {
    const [seal, q] = queue.entries().next().value;
    let a;
    try { a = await http("POST", "/v1/ask", { seal, recorded_ms: q.recorded_ms, grant: q.grant, grant_sig: q.grant_sig }); }
    catch (e) {
      if (busy(e.status)) return;                               // not reached: tried again in queueRetry ms
      await write({ not_signed: { seal, recorded_ms: q.recorded_ms, why: "STK refused it: " + e.status } });
      queue.delete(seal); continue;
    }
    keepGrant(a);
    if (!a.sig) await write({ not_signed: { seal, recorded_ms: q.recorded_ms, why: a.not_signed || "STK did not sign it" } });
    else { await write({ row: q.row, nonce: q.nonce, receipt: a.receipt, sig: a.sig, from_queue: true }); await saveKey(a.receipt.kid); }
    queue.delete(seal);
  }
}

// Waits until the queue is empty or ms pass: true when empty. Call it before a process ends.
export async function flush(ms = 30000) {
  const end = Date.now() + ms;
  while (Date.now() < end) {
    if (!queue.size) return true;
    if (!sending) startSender();
    await new Promise((r) => setTimeout(r, 50));
  }
  return !queue.size;
}

// Once, at the first ask: the last grant line of today's and yesterday's files, if it still holds by this machine's
// clock, and the rules lines kept with it.
async function readSaved() {
  if (saved.read || config.onRow) return;
  saved.read = true;
  let last = null; const rs = new Map();
  for (const d of [new Date(Date.now() - 86400000).toISOString().slice(0, 10), today()]) {
    let text = "";
    try { text = await readFile(join(config.rowsDir, d + ".jsonl"), "utf8"); } catch { continue; }
    for (const t of text.split("\n")) {
      if (!t.includes('"grant"') && !t.includes('"rules"')) continue;
      try {
        const l = JSON.parse(t);
        if (l.grant && l.grant.g && l.grant.sig && Object.keys(l.grant).length === 2) last = l.grant;
        if (l.rules && l.rules.version) rs.set(l.rules.version, l.rules);
      } catch {}
    }
  }
  for (const [v, r] of rs) {
    try { if (createHash("sha256").update(r.text, "utf8").digest("hex") === v) { decide(r.text, "", "unknown"); saved.rules.set(v, r); } } catch {}
  }
  const now = nowMs();
  if (last && !grant && last.g.issued_ms - 30000 <= now && now < last.g.expires_ms)
    grant = { g: last.g, sig: last.sig, until: performance.now() + (last.g.expires_ms - now) };
}

function rulesUnderGrant() {   // STK not reached at the first ask: the rules the kept grant names, if it holds and they were kept
  if (!grant || performance.now() >= grant.until) return false;
  const r = saved.rules.get(grant.g.rule_version);
  if (!r) return false;
  current = r;
  return true;
}

async function reloadQueue() {   // after a restart: queued lines of today and yesterday with no signed line yet go back in the queue, and to_tell lines not yet told are told
  const waiting = new Map(), gone = new Set(), kept = new Map(), told = new Set();
  for (const d of [new Date(Date.now() - 86400000).toISOString().slice(0, 10), today()]) {
    try {
      for (const t of (await readFile(join(config.rowsDir, d + ".jsonl"), "utf8")).split("\n")) {
        try {
          const l = JSON.parse(t);
          if (l.queued && l.queued.seal) waiting.set(l.queued.seal, l.queued);
          else if (l.receipt) gone.add(l.receipt.seal);
          for (const k of ["not_signed", "dequeued", "joined"]) if (l[k] && l[k].seal) gone.add(l[k].seal);
          if (l.to_tell && l.to_tell.id) kept.set(l.to_tell.id, l.to_tell);
          for (const k of ["joined", "not_told"]) if (l[k] && l[k].of) told.add(l[k].of);
        } catch {}
      }
    } catch {}
  }
  for (const [s, q] of waiting) if (!gone.has(s) && !queue.has(s)) queue.set(s, q);
  for (const [id, t] of kept) if (!told.has(id) && !tells.has(id)) tells.set(id, t);
  startSender();
  startTeller();
}

async function saveKey(kid) {   // the receipt's public key, once a day: the lines can be checked with nothing of STK running
  await doneToday();
  if (done.kids.has(kid)) return;
  done.kids.add(kid);
  try { const r = await http("GET", "/v1/rules?keys=1&kid=" + encodeURIComponent(kid), undefined, false); if (r.keys.length) await write({ key: r.keys[0] }); }
  catch { done.kids.delete(kid); }
}

// A person joined: told once for each finish this file knows the conversation got today (with its seal), or once
// without one. It never throws: STK not reached, it is told as soon as STK answers (a to_tell line until then).
// true, or false if your onRow function threw.
export async function joined(conversationId) {
  try { return await joinedNow(conversationId); } catch { return false; }
}

async function joinedNow(conversationId) {
  let seals = [null];
  const cid = conversationId === undefined || conversationId === null ? null : String(conversationId);
  if (cid !== null) {
    const p = cid + "\u0000";
    const set = await doneToday();
    const gone = [...set].filter((x) => x.startsWith(p)).sort();
    let found = gone.map((x) => done.seals.get(x) ?? null);
    if (!gone.length && (Date.now() / 1000) % 86400 < GRACE) found = [...done.yesterday].filter(([x]) => x.startsWith(p)).sort().map(([, s]) => s);
    if (!found.length && done.told.has(cid)) return true;   // told already today, and no finish of it since: not told again
    if (found.length) seals = found;
  }
  for (const s of seals) {
    if (s !== null && queue.has(s)) {                        // still in the queue: never sent, never billed
      queue.delete(s);
      await write({ dequeued: { time_ms: Date.now(), seal: s, why: "joined(" + (conversationId ?? "") + ") before STK signed it" } });
    } else await tell("joined(" + (conversationId ?? "") + ")", s);   // STK not reached: told as soon as it answers
    for (const book of [done.seals, done.yesterday]) for (const [x, v] of [...book]) if (s !== null && v === s) { book.delete(x); done.set.delete(x); }
    if (s === null && cid !== null) for (const x of [...done.set]) if (x.startsWith(cid + "\u0000")) done.set.delete(x);
  }
  if (cid !== null) done.told.add(cid);
  return true;
}

async function postJoined(why, seal = null, of = null) {   // POST /v1/joined (with the seal: it counts for that permission's day), and a line for it
  const a = await http("POST", "/v1/joined", seal ? { seal } : {});
  try { await write({ joined: { time_ms: Date.now(), day: a.day ?? null, seal, why, ...(of ? { of } : {}) } }); } catch {}   // told; only your onRow threw
}

// STK told a person joined, now: true. Not reached: kept as a to_tell line and told as soon as STK answers (false).
async function tell(why, seal = null) {
  try { await postJoined(why, seal); return true; } catch {}
  const t = { id: randomBytes(8).toString("hex"), time_ms: Date.now(), seal, why };
  try { await write({ to_tell: t }); } catch {}             // your onRow threw: kept while this process runs
  tells.set(t.id, t);
  startTeller();
  return false;
}

function startTeller() {
  if (telling || !tells.size) return;
  telling = true;
  sendTells().finally(() => { telling = false; if (tells.size) setTimeout(startTeller, config.queueRetry).unref?.(); });
}

async function sendTells() {   // in the order kept, as soon as STK answers: a joined line with of
  while (tells.size) {
    const [id, t] = tells.entries().next().value;
    try { await postJoined(t.why, t.seal ?? null, id); }
    catch (e) {
      if (busy(e.status)) return;                            // tried again in queueRetry ms
      try { await write({ not_told: { time_ms: Date.now(), seal: t.seal ?? null, of: id, why: "STK refused it: " + e.status } }); } catch {}
    }
    tells.delete(id);
  }
}

if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href) {
  if (process.argv.length < 3) { console.error("node stk.mjs <intent> [trigger]   (decides from STK's public rules; sends nothing)"); process.exit(1); }
  const r = await rules();
  console.log(decide(r.text, process.argv[2], process.argv[3] || "unknown"), "(rules " + r.version.slice(0, 12) + ")");
}
