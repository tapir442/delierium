# Full refresh, 2026-11-27 (refresh.sh)

- CPU: AMD Ryzen 9 7900X 12-Core Processor, 24 threads; RAM: 29 GiB
- OS: Linux 7.0.0-44-generic
- Python 3.14.4, SymPy 1.14.0, python-flint 0.9.0, delierium 2.7.2 + #121 (main 6b2eaf8, src unchanged since b4d967a)
- sympy-extras 0.0.2 (SymPy tools stage) and git fbca643a (extras-update.sh); REDUCE (redpsl); Maxima 5.49.0; GAP, Singular, CoCoA 5.4, Wolfram kernel /opt/Wolfram
- run: nice 19, at most 3 processes, per-task time and memory limits as in the scripts; idle machine (load 0.53 before start, 2026-11-28 09:07)
- times: 2026-11-28 09:06-17:49 (sympy-catalog 22 min, REDUCE packages 5.5 h, MathLie 2.2 h, solver 20 min, integrate 30 min)
- MathLie compare failed on names with non-ASCII letters (Rössler, Painlevé: garbled by Mathematica); names restored from the catalogue by index, compare rerun 17:51-18:14
