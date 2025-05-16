# Coverage Report

Total executable lines: 16
Covered lines: 16
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def hasChordIntersection(N, chords):
2: ✓     import heapq
3: ✓     new_chords = []
4: ✓     for a, b in chords:
5: ✓         if a > b:
6: ✓             a, b = b, a
7: ✓         new_chords.append((a, b))
8: ✓     new_chords.sort(key=lambda x: x[0])
9: ✓     open_heap = []
10: ✓     for c, d in new_chords:
11: ✓         while open_heap and open_heap[0] < c:
12: ✓             heapq.heappop(open_heap)
13: ✓         if open_heap and open_heap[0] < d:
14: ✓             return True
15: ✓         heapq.heappush(open_heap, d)
16: ✓     return False
```

## Complete Test File

```python
def hasChordIntersection(N, chords):
    import heapq
    new_chords = []
    for a, b in chords:
        if a > b:
            a, b = b, a
        new_chords.append((a, b))
    new_chords.sort(key=lambda x: x[0])
    open_heap = []
    for c, d in new_chords:
        while open_heap and open_heap[0] < c:
            heapq.heappop(open_heap)
        if open_heap and open_heap[0] < d:
            return True
        heapq.heappush(open_heap, d)
    return False

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = hasChordIntersection(3, [[1, 3], [4, 2], [5, 6]])
        assert result == True, f"Test 1 failed: got {result}, expected {True}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = hasChordIntersection(3, [[6, 1], [4, 3], [2, 5]])
        assert result == False, f"Test 2 failed: got {result}, expected {False}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = hasChordIntersection(4, [[2, 4], [3, 7], [8, 6], [5, 1]])
        assert result == True, f"Test 3 failed: got {result}, expected {True}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = hasChordIntersection(4, [[1, 2], [3, 4]])
        assert result == False, f"Test 4 failed: got {result}, expected {False}"
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
