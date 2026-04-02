#!/usr/bin/env bash

REPO_ROOT="/Users/alexkontorovich/Library/CloudStorage/Dropbox/sasha/Math/InProgress/Lean/PrimeNumberTheoremAnd"
WEB_DIR="$REPO_ROOT/blueprint/web"
STATE_DIR="${TMPDIR:-/tmp}/go_blueprint_prime_number_theorem_and"
PID_FILE="$STATE_DIR/server.pid"
PORT_FILE="$STATE_DIR/server.port"
LOG_FILE="$STATE_DIR/server.log"

ensure_blueprint_dependencies() {
  local tool
  for tool in lake leanblueprint python3 lsof ps; do
    if ! command -v "$tool" >/dev/null 2>&1; then
      printf 'Missing required tool: %s\n' "$tool" >&2
      exit 1
    fi
  done
}

cleanup_blueprint_state() {
  rm -f "$PID_FILE" "$PORT_FILE"
}

tracked_blueprint_pid() {
  if [[ ! -f "$PID_FILE" || ! -f "$PORT_FILE" ]]; then
    return 1
  fi

  local pid port listening_pid command_line
  pid="$(<"$PID_FILE")"
  port="$(<"$PORT_FILE")"

  [[ "$pid" =~ ^[0-9]+$ ]] || return 1
  [[ "$port" =~ ^[0-9]+$ ]] || return 1
  kill -0 "$pid" 2>/dev/null || return 1

  listening_pid="$(lsof -n -iTCP:"$port" -sTCP:LISTEN -t 2>/dev/null | head -n 1 || true)"
  [[ "$listening_pid" == "$pid" ]] || return 1

  command_line="$(ps -p "$pid" -o command= 2>/dev/null || true)"
  [[ "$command_line" == *"http.server"* ]] || return 1
  [[ "$command_line" == *"$WEB_DIR"* ]] || return 1

  printf '%s\n' "$pid"
}

tracked_blueprint_port() {
  local pid port
  pid="$(tracked_blueprint_pid)" || return 1
  port="$(<"$PORT_FILE")"
  [[ "$port" =~ ^[0-9]+$ ]] || return 1
  printf '%s\n' "$port"
}

find_open_blueprint_port() {
  local port=8000
  while lsof -n -iTCP:"$port" -sTCP:LISTEN -t >/dev/null 2>&1; do
    port=$((port + 1))
  done
  printf '%s\n' "$port"
}

start_blueprint_server() {
  local port="$1"
  mkdir -p "$STATE_DIR"
  : > "$LOG_FILE"

  nohup python3 -m http.server "$port" --directory "$WEB_DIR" >"$LOG_FILE" 2>&1 < /dev/null &
  local pid=$!
  printf '%s\n' "$pid" >"$PID_FILE"
  printf '%s\n' "$port" >"$PORT_FILE"

  sleep 1

  if tracked_blueprint_pid >/dev/null 2>&1; then
    return 0
  fi

  cleanup_blueprint_state
  printf 'Failed to start the blueprint server. Check %s\n' "$LOG_FILE" >&2
  return 1
}

stop_blueprint_server() {
  local pid
  pid="$(tracked_blueprint_pid)" || return 1

  kill "$pid" 2>/dev/null || true

  local attempt
  for attempt in 1 2 3 4 5 6 7 8 9 10; do
    if ! kill -0 "$pid" 2>/dev/null; then
      cleanup_blueprint_state
      return 0
    fi
    sleep 0.2
  done

  kill -9 "$pid" 2>/dev/null || true
  sleep 0.2

  if kill -0 "$pid" 2>/dev/null; then
    printf 'Could not stop blueprint server with pid %s\n' "$pid" >&2
    return 1
  fi

  cleanup_blueprint_state
  return 0
}
