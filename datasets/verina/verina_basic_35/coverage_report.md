# Coverage Report

Total executable lines: 4
Covered lines: 4
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def MoveZeroesToEnd(arr):
2: ✓     non_zeroes = [x for x in arr if x != 0]
3: ✓     zeros_count = len(arr) - len(non_zeroes)
4: ✓     return non_zeroes + [0] * zeros_count
```

## Complete Test File

```python
def MoveZeroesToEnd(arr):
    non_zeroes = [x for x in arr if x != 0]
    zeros_count = len(arr) - len(non_zeroes)
    return non_zeroes + [0] * zeros_count

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = MoveZeroesToEnd([0, 1, 0, 3, 12])
        assert result == [1, 3, 12, 0, 0], f"Test 1 failed: got {result}, expected {[1, 3, 12, 0, 0]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = MoveZeroesToEnd([0, 0, 1])
        assert result == [1, 0, 0], f"Test 2 failed: got {result}, expected {[1, 0, 0]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = MoveZeroesToEnd([1, 2, 3])
        assert result == [1, 2, 3], f"Test 3 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = MoveZeroesToEnd([0, 0, 0])
        assert result == [0, 0, 0], f"Test 4 failed: got {result}, expected {[0, 0, 0]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = MoveZeroesToEnd([])
        assert result == [], f"Test 5 failed: got {result}, expected {[]}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
