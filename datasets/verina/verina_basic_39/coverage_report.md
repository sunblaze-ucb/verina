# Coverage Report

Total executable lines: 5
Covered lines: 5
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def rotateRight(l, n):
2: ✓     if not l:
3: ✓         return l
4: ✓     n %= len(l)
5: ✓     return l[-n:] + l[:-n]
```

## Complete Test File

```python
def rotateRight(l, n):
    if not l:
        return l
    n %= len(l)
    return l[-n:] + l[:-n]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = rotateRight([1, 2, 3, 4, 5], 2)
        assert result == [4, 5, 1, 2, 3], f"Test 1 failed: got {result}, expected {[4, 5, 1, 2, 3]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = rotateRight([1, 2, 3, 4, 5], 7)
        assert result == [4, 5, 1, 2, 3], f"Test 2 failed: got {result}, expected {[4, 5, 1, 2, 3]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = rotateRight([1, 2, 3, 4, 5], 0)
        assert result == [1, 2, 3, 4, 5], f"Test 3 failed: got {result}, expected {[1, 2, 3, 4, 5]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = rotateRight([], 2)
        assert result == [], f"Test 4 failed: got {result}, expected {[]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
