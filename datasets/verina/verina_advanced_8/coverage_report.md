# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def canCompleteCircuit(gas, cost):
2: ✓     if sum(gas) < sum(cost):
3: ✓         return -1
4: ✓     start = 0
5: ✓     current_gas = 0
6: ✓     for i in range(len(gas)):
7: ✓         current_gas += gas[i] - cost[i]
8: ✓         if current_gas < 0:
9: ✓             start = i + 1
10: ✓             current_gas = 0
11: ✓     return start
```

## Complete Test File

```python
def canCompleteCircuit(gas, cost):
    if sum(gas) < sum(cost):
        return -1
    start = 0
    current_gas = 0
    for i in range(len(gas)):
        current_gas += gas[i] - cost[i]
        if current_gas < 0:
            start = i + 1
            current_gas = 0
    return start

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = canCompleteCircuit([1, 2, 3, 4, 5], [3, 4, 5, 1, 2])
        assert result == 3, f"Test 1 failed: got {result}, expected {3}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = canCompleteCircuit([2, 3, 4], [3, 4, 3])
        assert result == -1, f"Test 2 failed: got {result}, expected {-1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = canCompleteCircuit([5, 1, 2, 3, 4], [4, 4, 1, 5, 1])
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = canCompleteCircuit([3, 3, 4], [3, 4, 4])
        assert result == -1, f"Test 4 failed: got {result}, expected {-1}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = canCompleteCircuit([1, 2, 3], [1, 2, 3])
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = canCompleteCircuit([1, 2, 3, 4], [2, 2, 2, 2])
        assert result == 1, f"Test 6 failed: got {result}, expected {1}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = canCompleteCircuit([0, 0, 0], [1, 1, 1])
        assert result == -1, f"Test 7 failed: got {result}, expected {-1}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
