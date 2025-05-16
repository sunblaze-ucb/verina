# Coverage Report

Total executable lines: 11
Covered lines: 11
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def isPeakValley(lst):
2: ✓     if len(lst) < 3:
3: ✓         return False
4: ✓     i = 0
5: ✓     # strictly increasing phase
6: ✓     while i < len(lst) - 1 and lst[i] < lst[i+1]:
7: ✓         i += 1
8: ✓     # i should not be the first or last index
9: ✓     if i == 0 or i == len(lst) - 1:
10: ✓         return False
11: ✓     # strictly decreasing phase
12: ✓     while i < len(lst) - 1 and lst[i] > lst[i+1]:
13: ✓         i += 1
14: ✓     return i == len(lst) - 1
```

## Complete Test File

```python
def isPeakValley(lst):
    if len(lst) < 3:
        return False
    i = 0
    # strictly increasing phase
    while i < len(lst) - 1 and lst[i] < lst[i+1]:
        i += 1
    # i should not be the first or last index
    if i == 0 or i == len(lst) - 1:
        return False
    # strictly decreasing phase
    while i < len(lst) - 1 and lst[i] > lst[i+1]:
        i += 1
    return i == len(lst) - 1

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = isPeakValley([1, 3, 5, 2, 1])
        assert result == True, f"Test 1 failed: got {result}, expected {True}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = isPeakValley([1, 2, 3, 4, 5])
        assert result == False, f"Test 2 failed: got {result}, expected {False}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = isPeakValley([])
        assert result == False, f"Test 3 failed: got {result}, expected {False}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = isPeakValley([1])
        assert result == False, f"Test 4 failed: got {result}, expected {False}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = isPeakValley([1, 1, 1, 1, 1])
        assert result == False, f"Test 5 failed: got {result}, expected {False}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = isPeakValley([1, 10, 100, 1])
        assert result == True, f"Test 6 failed: got {result}, expected {True}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
