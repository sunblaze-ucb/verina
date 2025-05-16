# Coverage Report

Total executable lines: 25
Covered lines: 25
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def maxCoverageAfterRemovingOne(intervals):
2: ✓     n = len(intervals)
3: ✓     events = []
4: ✓     for i, (start, end) in enumerate(intervals):
5: ✓         events.append((start, 1, i))
6: ✓         events.append((end, -1, i))
7: ✓     events.sort(key=lambda x: (x[0], -x[1]))
8: ✓     total = 0
9: ✓     unique = [0] * n
10: ✓     active = set()
11: ✓     last_time = events[0][0]
12: ✓     for time, typ, idx in events:
13: ✓         if time > last_time:
14: ✓             duration = time - last_time
15: ✓             if active:
16: ✓                 total += duration
17: ✓             if len(active) == 1:
18: ✓                 # Only one interval active, add to its unique coverage.
19: ✓                 guard = next(iter(active))
20: ✓                 unique[guard] += duration
21: ✓             last_time = time
22: ✓         if typ == 1:
23: ✓             active.add(idx)
24: ✓         else:
25: ✓             active.remove(idx)
26: ✓     best = total - min(unique)
27: ✓     return best
```

## Complete Test File

```python
def maxCoverageAfterRemovingOne(intervals):
    n = len(intervals)
    events = []
    for i, (start, end) in enumerate(intervals):
        events.append((start, 1, i))
        events.append((end, -1, i))
    events.sort(key=lambda x: (x[0], -x[1]))
    total = 0
    unique = [0] * n
    active = set()
    last_time = events[0][0]
    for time, typ, idx in events:
        if time > last_time:
            duration = time - last_time
            if active:
                total += duration
            if len(active) == 1:
                # Only one interval active, add to its unique coverage.
                guard = next(iter(active))
                unique[guard] += duration
            last_time = time
        if typ == 1:
            active.add(idx)
        else:
            active.remove(idx)
    best = total - min(unique)
    return best

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = maxCoverageAfterRemovingOne([(1, 3), (2, 5), (6, 8)])
        assert result == 5, f"Test 1 failed: got {result}, expected {5}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = maxCoverageAfterRemovingOne([(1, 4), (2, 6), (8, 10), (9, 12)])
        assert result == 8, f"Test 2 failed: got {result}, expected {8}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = maxCoverageAfterRemovingOne([(1, 2), (2, 3), (3, 4)])
        assert result == 2, f"Test 3 failed: got {result}, expected {2}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = maxCoverageAfterRemovingOne([(1, 10), (2, 3), (4, 5)])
        assert result == 9, f"Test 4 failed: got {result}, expected {9}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = maxCoverageAfterRemovingOne([(5, 6), (1, 2), (3, 4)])
        assert result == 2, f"Test 5 failed: got {result}, expected {2}"
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
