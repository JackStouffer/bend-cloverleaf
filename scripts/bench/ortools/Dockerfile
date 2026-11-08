# A throwaway image for comparing the Bend planner with Google OR-Tools. It is a
# benchmark tool only: the app never runs it, and this is the one place Python
# is allowed, because OR-Tools has no Node binding.
#   docker build -t cloverleaf-ortools scripts/bench/ortools
#   docker run --rm -m 2g --memory-swap 2g -v "$PWD/data/synth:/synth:ro" cloverleaf-ortools /synth/georgia 120
FROM python:3.12-slim
RUN pip install --no-cache-dir ortools==9.12.4544
COPY compare.py /compare.py
ENTRYPOINT ["python", "/compare.py"]
