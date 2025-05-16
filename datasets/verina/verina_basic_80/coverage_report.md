# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def only_once(a, key):
2: ✓     return a.count(key) == 1
```

## Complete Test File

```python
def only_once(a, key):
    return a.count(key) == 1

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = only_once([1, 2, 3, 4], 2)
        assert result == 'true', f"Test 1 failed: got {result}, expected {'true'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = only_once([1, 2, 2, 3, 4], 2)
        assert result == 'false', f"Test 2 failed: got {result}, expected {'false'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = only_once([1, 1, 1, 1], 1)
        assert result == 'false', f"Test 3 failed: got {result}, expected {'false'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = only_once([10], 10)
        assert result == 'true', f"Test 4 failed: got {result}, expected {'true'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = only_once([], 5)
        assert result == 'false', f"Test 5 failed: got {result}, expected {'false'}"
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
