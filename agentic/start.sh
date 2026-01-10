#!/bin/bash
#
# Agentic Theorem Proving System - Startup Script
#
# Usage:
#   ./agentic/start.sh          # Interactive mode (shows logs)
#   ./agentic/start.sh daemon   # Daemon mode (background)
#   ./agentic/start.sh stop     # Stop all services
#   ./agentic/start.sh status   # Check status
#

set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
LOG_DIR="$SCRIPT_DIR/logs"
PID_DIR="$SCRIPT_DIR/pids"

mkdir -p "$LOG_DIR" "$PID_DIR"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

log() {
    echo -e "${GREEN}[$(date '+%H:%M:%S')]${NC} $1"
}

error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

# Check dependencies
check_deps() {
    log "Checking dependencies..."

    if ! command -v python3 &> /dev/null; then
        error "python3 not found"
        exit 1
    fi

    if ! command -v aristotle &> /dev/null; then
        warn "aristotle CLI not found - some features may not work"
    fi

    # Run health check
    cd "$PROJECT_DIR"
    python3 "$SCRIPT_DIR/health_check.py"
}

# Initialize the system
init() {
    log "Initializing agentic system..."
    cd "$PROJECT_DIR"
    python3 "$SCRIPT_DIR/setup.py" --all
}

# Start orchestrator
start_orchestrator() {
    local mode=$1
    log "Starting orchestrator..."

    cd "$PROJECT_DIR"

    if [ "$mode" == "daemon" ]; then
        nohup python3 "$SCRIPT_DIR/orchestrator.py" \
            > "$LOG_DIR/orchestrator.log" 2>&1 &
        echo $! > "$PID_DIR/orchestrator.pid"
        log "Orchestrator started (PID: $(cat $PID_DIR/orchestrator.pid))"
    else
        python3 "$SCRIPT_DIR/orchestrator.py" &
        ORCHESTRATOR_PID=$!
    fi
}

# Start validator pipeline
start_validator() {
    local mode=$1
    log "Starting validator pipeline..."

    cd "$PROJECT_DIR"

    if [ "$mode" == "daemon" ]; then
        nohup python3 "$SCRIPT_DIR/validators/pipeline.py" --watch \
            > "$LOG_DIR/validator.log" 2>&1 &
        echo $! > "$PID_DIR/validator.pid"
        log "Validator started (PID: $(cat $PID_DIR/validator.pid))"
    else
        python3 "$SCRIPT_DIR/validators/pipeline.py" --watch &
        VALIDATOR_PID=$!
    fi
}

# Start generator pool
start_generators() {
    log "Starting initial generator batch..."

    cd "$PROJECT_DIR"
    python3 "$SCRIPT_DIR/generators/pool.py" --count 30

    log "Initial generators complete"
}

# Start dashboard
start_dashboard() {
    local mode=$1
    log "Starting dashboard..."

    cd "$PROJECT_DIR"

    if [ "$mode" == "daemon" ]; then
        nohup python3 "$SCRIPT_DIR/monitor/dashboard.py" --watch \
            > "$LOG_DIR/dashboard.log" 2>&1 &
        echo $! > "$PID_DIR/dashboard.pid"
        log "Dashboard started (PID: $(cat $PID_DIR/dashboard.pid))"
        log "View logs: tail -f $LOG_DIR/dashboard.log"
    else
        python3 "$SCRIPT_DIR/monitor/dashboard.py" --watch
    fi
}

# Stop all services
stop_all() {
    log "Stopping all services..."

    for pid_file in "$PID_DIR"/*.pid; do
        if [ -f "$pid_file" ]; then
            pid=$(cat "$pid_file")
            service=$(basename "$pid_file" .pid)
            if kill -0 "$pid" 2>/dev/null; then
                kill "$pid"
                log "Stopped $service (PID: $pid)"
            fi
            rm "$pid_file"
        fi
    done

    log "All services stopped"
}

# Check status
check_status() {
    echo "======================================"
    echo "AGENTIC SYSTEM STATUS"
    echo "======================================"

    for service in orchestrator validator dashboard; do
        pid_file="$PID_DIR/$service.pid"
        if [ -f "$pid_file" ]; then
            pid=$(cat "$pid_file")
            if kill -0 "$pid" 2>/dev/null; then
                echo -e "  $service: ${GREEN}RUNNING${NC} (PID: $pid)"
            else
                echo -e "  $service: ${RED}DEAD${NC} (stale PID file)"
            fi
        else
            echo -e "  $service: ${YELLOW}NOT STARTED${NC}"
        fi
    done

    echo ""
    echo "Log files:"
    ls -la "$LOG_DIR"/*.log 2>/dev/null || echo "  (no logs yet)"

    echo ""
    echo "Quick stats:"
    cd "$PROJECT_DIR"
    python3 "$SCRIPT_DIR/monitor/dashboard.py" --json 2>/dev/null | python3 -c "
import sys, json
try:
    d = json.load(sys.stdin)
    q = d.get('queue', {})
    print(f\"  Queue depth: {q.get('validated_pending', 0)} ready\")
    slots = d.get('slots', [])
    active = sum(1 for s in slots if s.get('status') != 'empty')
    print(f\"  Active slots: {active}/15\")
except:
    pass
" 2>/dev/null || true
}

# Main
case "${1:-}" in
    daemon)
        check_deps
        init
        start_orchestrator daemon
        start_validator daemon
        start_generators
        log "System started in daemon mode"
        log "Use './agentic/start.sh status' to check status"
        log "Use './agentic/start.sh stop' to stop"
        ;;
    stop)
        stop_all
        ;;
    status)
        check_status
        ;;
    init)
        init
        ;;
    dashboard)
        start_dashboard interactive
        ;;
    "")
        # Interactive mode
        check_deps
        init

        log "Starting in interactive mode (Ctrl+C to stop)..."
        log "This will show the dashboard. Services run in background."

        # Start background services
        start_orchestrator daemon
        start_validator daemon
        start_generators

        # Show dashboard in foreground
        trap "stop_all" EXIT
        start_dashboard interactive
        ;;
    *)
        echo "Usage: $0 [daemon|stop|status|init|dashboard]"
        echo ""
        echo "Commands:"
        echo "  (none)    Interactive mode - shows dashboard, Ctrl+C stops all"
        echo "  daemon    Start all services in background"
        echo "  stop      Stop all services"
        echo "  status    Check service status"
        echo "  init      Initialize database only"
        echo "  dashboard Show dashboard only"
        exit 1
        ;;
esac
