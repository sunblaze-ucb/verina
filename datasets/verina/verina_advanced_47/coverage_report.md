# Coverage Report

Total executable lines: 8
Covered lines: 8
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def mergeIntervals(intervals):
2: ✓     intervals.sort(key=lambda x: x[0])
3: ✓     merged = []
4: ✓     for interval in intervals:
5: ✓         if not merged or merged[-1][1] < interval[0]:
6: ✓             merged.append(interval)
7: ✓         else:
8: ✓             merged[-1][1] = max(merged[-1][1], interval[1])
9: ✓     return merged
```

## Complete Test File

```python
def mergeIntervals(intervals):
    intervals.sort(key=lambda x: x[0])
    merged = []
    for interval in intervals:
        if not merged or merged[-1][1] < interval[0]:
            merged.append(interval)
        else:
            merged[-1][1] = max(merged[-1][1], interval[1])
    return merged

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = mergeIntervals([(1, 3), (2, 6), (8, 10), (15, 18)])
        assert result == [(1, 6), (8, 10), (15, 18)], f"Test 1 failed: got {result}, expected {[(1, 6), (8, 10), (15, 18)]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = mergeIntervals([(1, 4), (4, 5)])
        assert result == [(1, 5)], f"Test 2 failed: got {result}, expected {[(1, 5)]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = mergeIntervals([(1, 10), (2, 3), (4, 5)])
        assert result == [(1, 10)], f"Test 3 failed: got {result}, expected {[(1, 10)]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = mergeIntervals([(1, 2), (3, 4), (5, 6)])
        assert result == [(1, 2), (3, 4), (5, 6)], f"Test 4 failed: got {result}, expected {[(1, 2), (3, 4), (5, 6)]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = mergeIntervals([(5, 6), (1, 3), (2, 4)])
        assert result == [(1, 4), (5, 6)], f"Test 5 failed: got {result}, expected {[(1, 4), (5, 6)]}"
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
