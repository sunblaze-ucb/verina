# Coverage Report

Total executable lines: 4
Covered lines: 4
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def Triple(x):
2: ✓     if x < 18:
3: ✓         return 3 * x
4: ✓     else:
5: ✓         return 3 * x
```

## Complete Test File

```python
def Triple(x):
    if x < 18:
        return 3 * x
    else:
        return 3 * x

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = Triple(10)
        assert result == 30, f"Test 1 failed: got {result}, expected {30}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = Triple(18)
        assert result == 54, f"Test 2 failed: got {result}, expected {54}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = Triple(0)
        assert result == 0, f"Test 3 failed: got {result}, expected {0}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = Triple(-5)
        assert result == -15, f"Test 4 failed: got {result}, expected {-15}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = Triple(25)
        assert result == 75, f"Test 5 failed: got {result}, expected {75}"
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
