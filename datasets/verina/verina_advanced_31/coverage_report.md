# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def longestIncreasingSubseqLength(xs):
2: ✓     import bisect
3: ✓     lis = []
4: ✓     for x in xs:
5: ✓         pos = bisect.bisect_left(lis, x)
6: ✓         if pos == len(lis):
7: ✓             lis.append(x)
8: ✓         else:
9: ✓             lis[pos] = x
10: ✓     return len(lis)
```

## Complete Test File

```python
def longestIncreasingSubseqLength(xs):
    import bisect
    lis = []
    for x in xs:
        pos = bisect.bisect_left(lis, x)
        if pos == len(lis):
            lis.append(x)
        else:
            lis[pos] = x
    return len(lis)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = longestIncreasingSubseqLength([1, 2, 3, 4])
        assert result == 4, f"Test 1 failed: got {result}, expected {4}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = longestIncreasingSubseqLength([4, 3, 2, 1])
        assert result == 1, f"Test 2 failed: got {result}, expected {1}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = longestIncreasingSubseqLength([1, 3, 2, 4, 0, 5])
        assert result == 4, f"Test 3 failed: got {result}, expected {4}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = longestIncreasingSubseqLength([])
        assert result == 0, f"Test 4 failed: got {result}, expected {0}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = longestIncreasingSubseqLength([5, 1, 6, 2, 7])
        assert result == 3, f"Test 5 failed: got {result}, expected {3}"
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
