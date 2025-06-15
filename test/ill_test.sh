#!/bin/bash 

# ILL Test Suite - Tests intuitionistic linear logic implementation
# This script takes inputs from ./ill_tests/<test name>/in.txt 
# then sends them to the backend, where the output is compared with ./ill_tests/<test name>/out.txt

# Server configuration
SERVER_URL="http://localhost:3000"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TESTS_DIR="$SCRIPT_DIR/ill_tests"

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Colored message functions
print_green() {
    echo -e "${GREEN}$1${NC}"
}

print_red() {
    echo -e "${RED}$1${NC}"
}

print_yellow() {
    echo -e "${YELLOW}$1${NC}"
}

print_blue() {
    echo -e "${BLUE}$1${NC}"
}

# Test if server is online
test_server_online() {
    print_blue "Testing server connection at $SERVER_URL..."
    if curl -s --connect-timeout 5 "$SERVER_URL/parse_sequent/" > /dev/null 2>&1; then
        print_green "✓ Server is online"
        return 0
    else
        print_red "✗ Server is offline or unreachable at $SERVER_URL"
        print_yellow "Please start the server with: dune exec ./main.exe"
        return 1
    fi
}

# Send JSON to server endpoint and get response
call_server_endpoint() {
    local endpoint="$1"
    local json_data="$2"
    local method="${3:-POST}"
    
    if [ "$method" = "GET" ]; then
        curl -s "$SERVER_URL/$endpoint" 2>/dev/null
    else
        curl -s -X POST \
             -H "Content-Type: application/json" \
             -d "$json_data" \
             "$SERVER_URL/$endpoint" 2>/dev/null
    fi
}

# Normalize JSON for comparison (remove whitespace differences)
normalize_json() {
    echo "$1" | jq -c -S . 2>/dev/null || echo "$1"
}

# Run a single test
run_test() {
    local test_name="$1"
    local test_dir="$TESTS_DIR/$test_name"
    local input_file="$test_dir/in.txt"
    local expected_file="$test_dir/out.txt"
    
    if [ ! -f "$input_file" ]; then
        print_red "✗ $test_name: Missing input file $input_file"
        return 1
    fi
    
    if [ ! -f "$expected_file" ]; then
        print_red "✗ $test_name: Missing expected output file $expected_file"
        return 1
    fi
    
    # Read input and expected output
    local input_data
    input_data=$(cat "$input_file")
    local expected_output
    expected_output=$(cat "$expected_file")
    
    # Determine endpoint based on test type
    local endpoint
    if echo "$input_data" | grep -q '"sequent"'; then
        endpoint="parse_sequent/$(echo "$input_data" | jq -r '.sequent' | sed 's/ //g')?intuitionisticMode=1"
        # For parse_sequent, use GET request
        local actual_output
        actual_output=$(call_server_endpoint "$endpoint" "" "GET")
    else
        # For rule application, use POST request
        endpoint="apply_rule"
        local actual_output
        actual_output=$(call_server_endpoint "$endpoint" "$input_data")
    fi
    
    # Normalize both outputs for comparison
    local normalized_expected
    normalized_expected=$(normalize_json "$expected_output")
    local normalized_actual
    normalized_actual=$(normalize_json "$actual_output")
    
    # Compare outputs
    if [ "$normalized_expected" = "$normalized_actual" ]; then
        print_green "✓ $test_name: PASS"
        return 0
    else
        print_red "✗ $test_name: FAIL"
        echo "  Expected: $expected_output"
        echo "  Actual:   $actual_output"
        return 1
    fi
}

# Main function
main() {
    print_blue "=== ILL Test Suite ==="
    echo
    
    # Test if server is online, if offline exit 
    if ! test_server_online; then
        exit 1
    fi
    echo
    
    # Initialize counters
    local passed=0
    local failed=0
    local total=0
    
    # Check if tests directory exists
    if [ ! -d "$TESTS_DIR" ]; then
        print_red "Error: Tests directory not found at $TESTS_DIR"
        exit 1
    fi
    
    # For each test in ./ill_tests/
    print_blue "Running ILL tests..."
    for test_dir in "$TESTS_DIR"/*; do
        if [ -d "$test_dir" ]; then
            test_name=$(basename "$test_dir")
            
            # Skip README.md and any non-test directories
            if [ "$test_name" = "README.md" ] || [ ! -f "$test_dir/in.txt" ]; then
                continue
            fi
            
            total=$((total + 1))
            
            if run_test "$test_name"; then
                passed=$((passed + 1))
            else
                failed=$((failed + 1))
            fi
        fi
    done
    
    # Print summary
    echo
    print_blue "=== Test Results ==="
    print_green "Tests passed: $passed"
    if [ $failed -gt 0 ]; then
        print_red "Tests failed: $failed"
    else
        print_green "Tests failed: $failed"
    fi
    print_blue "Total tests: $total"
    
    # Exit with appropriate code
    if [ $failed -eq 0 ] && [ $total -gt 0 ]; then
        print_green "All tests passed! ✓"
        exit 0
    elif [ $total -eq 0 ]; then
        print_yellow "No tests found to run"
        exit 1
    else
        print_red "Some tests failed ✗"
        exit 1
    fi
}

# Run main function
main "$@"
