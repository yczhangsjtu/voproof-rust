"""
This tool is used to parse the time info printed by running
```
cargo test --features "print-trace" test_case -- --nocapture
```
in the `voproof` directory. The print result is of the following format:

```
..Start:   Procedure Name
....Start:   SubProcedure Name
....End:     SubProcedure Name ........................time
..End:     Procedure Name .............................time
```
This tool collects all the information and join the time of the same
procedure.
"""

import re
import sys

lines = sys.stdin.readlines()
total_times = {}
target_name = "Proving"
started = False
for line in lines:
  line = line.strip()
  if re.match(r"·*Start:\s*" + target_name, line):
    started = True
  if not started:
    continue

  match = re.match(r"·*End:\s*([^\.]+\S) \.+([\d\.]+)(m|µ|n)?s", line)
  if match is not None:
    name = match.group(1)
    var_match = re.match(r"(.*) of (size|degree|density).*", name)
    if var_match is not None:
      name = var_match.group(1)

    value = float(match.group(2))
    unit = match.group(3)
    if unit is None:
      """
      We unify the unit to milliseconds
      """
      value *= 1000
    elif unit == "m":
      pass
    elif unit == "µ":
      value /= 1000
    elif unit == "n":
      value /= 1000000
    else:
      raise ValueError(f"Invalid unit {unit}")

    if name not in total_times:
      total_times[name] = 0
    total_times[name] += value
    if name == target_name:
      started = False

items = [(key, value) for key, value in total_times.items()]
items.sort(key=lambda item: item[1])
max_len = max(len(key) for key, value in total_times.items())

for key, value in items:
  print(f"{key:<{max_len}}  ", f"{value:.3f}ms ({value/1000:.3f}s)")
