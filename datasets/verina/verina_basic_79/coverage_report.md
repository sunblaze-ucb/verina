# Coverage Report

Total executable lines: 10
Covered lines: 10
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def onlineMax(a, x):
2: ✓     m = max(a[:x])
3: ✓     p = None
4: ✓     for i in range(x, len(a)):
5: ✓         if a[i] > m:
6: ✓             p = i
7: ✓             break
8: ✓     if p is None:
9: ✓         p = len(a) - 1
10: ✓     return (m, p)
```

## Complete Test File

```python
def onlineMax(a, x):
    m = max(a[:x])
    p = None
    for i in range(x, len(a)):
        if a[i] > m:
            p = i
            break
    if p is None:
        p = len(a) - 1
    return (m, p)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = onlineMax([3, 7, 5, 2, 9], 3)
        assert result == '(7, 4)', f"Test 1 failed: got {result}, expected {'(7, 4)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = onlineMax([10, 10, 5, 1], 2)
        assert result == '(10, 3)', f"Test 2 failed: got {result}, expected {'(10, 3)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = onlineMax([1, 3, 3, 3, 1], 2)
        assert result == '(3, 4)', f"Test 3 failed: got {result}, expected {'(3, 4)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = onlineMax([5, 4, 4, 6, 2], 2)
        assert result == '(5, 3)', f"Test 4 failed: got {result}, expected {'(5, 3)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = onlineMax([2, 8, 7, 7, 7], 3)
        assert result == '(8, 4)', f"Test 5 failed: got {result}, expected {'(8, 4)'}"
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
