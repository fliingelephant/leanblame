/-
UTC timestamps. Records carry native TOML datetimes in UTC; JSON carries the
same instant as an ISO 8601 string. Both render as `YYYY-MM-DDTHH:MM:SSZ`.
-/
import Std.Time
import Lake.Toml

namespace LeanBlame

/-- A UTC instant with one-second resolution. -/
structure UtcTime where
  year : Nat
  month : Nat
  day : Nat
  hour : Nat
  minute : Nat
  second : Nat
  deriving Inhabited, DecidableEq, Repr

namespace UtcTime

instance : Ord UtcTime where
  compare a b :=
    (compare a.year b.year).then <| (compare a.month b.month).then <|
      (compare a.day b.day).then <| (compare a.hour b.hour).then <|
        (compare a.minute b.minute).then (compare a.second b.second)

instance : LT UtcTime := ltOfOrd
instance : LE UtcTime := leOfOrd

private def pad (n width : Nat) : String :=
  let s := toString n
  "".pushn '0' (width - s.length) ++ s

/-- `YYYY-MM-DDTHH:MM:SSZ`: the TOML datetime and the ISO 8601 string. -/
def toIso (t : UtcTime) : String :=
  s!"{pad t.year 4}-{pad t.month 2}-{pad t.day 2}T{pad t.hour 2}:{pad t.minute 2}:{pad t.second 2}Z"

instance : ToString UtcTime := ⟨toIso⟩

/-- Civil date from days since 1970-01-01 (Howard Hinnant's algorithm), for days ≥ 0. -/
def ofEpochSeconds (secs : Nat) : UtcTime :=
  let days := secs / 86400
  let rem := secs % 86400
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if m ≤ 2 then 1 else 0)
  { year := y, month := m, day := d, hour := rem / 3600, minute := rem % 3600 / 60, second := rem % 60 }

/-- The current instant. -/
def now : IO UtcTime := do
  let ts ← Std.Time.Timestamp.now
  let secs := ts.toSecondsSinceUnixEpoch.val
  return ofEpochSeconds secs.toNat

/-- From a TOML datetime; only offset datetimes in UTC (`Z` or `+00:00`) are accepted. -/
def ofToml? (dt : Lake.Toml.DateTime) : Except String UtcTime :=
  match dt with
  | .offsetDateTime d t offset? =>
    let utc := match offset? with
      | none => true
      | some (_, o) => o.hour == 0 && o.minute == 0
    if utc then
      .ok { year := d.year, month := d.month, day := d.day,
            hour := t.hour, minute := t.minute, second := t.second }
    else .error "date must be in UTC (offset Z)"
  | _ => .error "date must be an offset datetime in UTC, e.g. 2026-10-23T14:02:11Z"

/-- From an ISO 8601 string as written by `toIso` (fractional seconds and `+00:00` accepted). -/
def ofIso? (s : String) : Except String UtcTime :=
  match Lake.Toml.DateTime.ofString? s with
  | some dt => ofToml? dt
  | none => .error s!"not an ISO 8601 UTC datetime: {s}"

end UtcTime

end LeanBlame
