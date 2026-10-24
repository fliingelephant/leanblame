/-
UTC instants, `Std.Time.Timestamp` with one-second resolution. Records carry
native TOML datetimes in UTC; JSON carries the same instant as an ISO 8601
string. Both render as `YYYY-MM-DDTHH:MM:SSZ`.
-/
import Std.Time
import Lake.Toml

namespace Std.Time.Timestamp

/-- The current instant, truncated to seconds. -/
def nowSeconds : IO Timestamp :=
  return .ofSecondsSinceUnixEpoch (← Timestamp.now).toSecondsSinceUnixEpoch

/-- `YYYY-MM-DDTHH:MM:SSZ`: the TOML datetime and the ISO 8601 string. -/
def toIso (t : Timestamp) : String := (DateTime.ofTimestamp t .UTC).toISO8601String

/-- From a TOML datetime; only offset datetimes in UTC (`Z` or `+00:00`) are accepted. Fractions of
a second are dropped. -/
def ofToml? : Lake.Toml.DateTime → Except String Timestamp
  | .offsetDateTime d t offset? =>
    if offset?.any fun (_, o) => o.hour != 0 || o.minute != 0 then .error "date must be in UTC (offset Z)"
    else .ok <| PlainDateTime.toTimestamp (zr := .UTC)
      { date := .ofYearMonthDayClip (.ofNat d.year) (.clip d.month (by decide)) (.clip d.day (by decide))
        time := .ofHourMinuteSeconds (.clip t.hour (by decide)) (.clip t.minute (by decide))
          (.clip t.second (by decide)) }
  | _ => .error "date must be an offset datetime in UTC, e.g. 2026-10-23T14:02:11Z"

end Std.Time.Timestamp
