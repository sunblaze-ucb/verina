# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def remove_front(a):
2: ✓     return a[1:]
```

## Complete Test File

```python
def remove_front(a):
    return a[1:]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = remove_front([1, 2, 3, 4, 5])
        assert result == [2, 3, 4, 5], f"Test 1 failed: got {result}, expected {[2, 3, 4, 5]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = remove_front([10, 20, 30])
        assert result == [20, 30], f"Test 2 failed: got {result}, expected {[20, 30]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = remove_front([0, -1, -2, -3])
        assert result == [-1, -2, -3], f"Test 3 failed: got {result}, expected {[-1, -2, -3]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = remove_front([7])
        assert result == [], f"Test 4 failed: got {result}, expected {[]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = remove_front([100, 0, 50])
        assert result == [0, 50], f"Test 5 failed: got {result}, expected {[0, 50]}"
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
