# Coverage Report

Total executable lines: 25
Covered lines: 25
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def mergeSorted(a1, a2):
2: ✓     i, j = 0, 0
3: ✓     merged = []
4: ✓     while i < len(a1) and j < len(a2):
5: ✓         if a1[i] < a2[j]:
6: ✓             if not merged or merged[-1] != a1[i]:
7: ✓                 merged.append(a1[i])
8: ✓             i += 1
9: ✓         elif a1[i] > a2[j]:
10: ✓             if not merged or merged[-1] != a2[j]:
11: ✓                 merged.append(a2[j])
12: ✓             j += 1
13: ✓         else:
14: ✓             if not merged or merged[-1] != a1[i]:
15: ✓                 merged.append(a1[i])
16: ✓             i += 1
17: ✓             j += 1
18: ✓     while i < len(a1):
19: ✓         if not merged or merged[-1] != a1[i]:
20: ✓             merged.append(a1[i])
21: ✓         i += 1
22: ✓     while j < len(a2):
23: ✓         if not merged or merged[-1] != a2[j]:
24: ✓             merged.append(a2[j])
25: ✓         j += 1
26: ✓     return merged
```

## Complete Test File

```python
def mergeSorted(a1, a2):
    i, j = 0, 0
    merged = []
    while i < len(a1) and j < len(a2):
        if a1[i] < a2[j]:
            if not merged or merged[-1] != a1[i]:
                merged.append(a1[i])
            i += 1
        elif a1[i] > a2[j]:
            if not merged or merged[-1] != a2[j]:
                merged.append(a2[j])
            j += 1
        else:
            if not merged or merged[-1] != a1[i]:
                merged.append(a1[i])
            i += 1
            j += 1
    while i < len(a1):
        if not merged or merged[-1] != a1[i]:
            merged.append(a1[i])
        i += 1
    while j < len(a2):
        if not merged or merged[-1] != a2[j]:
            merged.append(a2[j])
        j += 1
    return merged

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = mergeSorted([1, 3, 5], [2, 4, 6])
        assert result == [1, 2, 3, 4, 5, 6], f"Test 1 failed: got {result}, expected {[1, 2, 3, 4, 5, 6]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = mergeSorted([], [1, 2, 3])
        assert result == [1, 2, 3], f"Test 2 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = mergeSorted([1, 2, 3], [])
        assert result == [1, 2, 3], f"Test 3 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = mergeSorted([], [])
        assert result == [], f"Test 4 failed: got {result}, expected {[]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = mergeSorted([1, 1, 2], [1, 2, 2])
        assert result == [1, 1, 1, 2, 2, 2], f"Test 5 failed: got {result}, expected {[1, 1, 1, 2, 2, 2]}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = mergeSorted([10, 20, 30], [5, 15, 25])
        assert result == [5, 10, 15, 20, 25, 30], f"Test 6 failed: got {result}, expected {[5, 10, 15, 20, 25, 30]}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = mergeSorted([1, 3, 5, 7, 9], [2, 4, 6, 8, 10])
        assert result == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10], f"Test 7 failed: got {result}, expected {[1, 2, 3, 4, 5, 6, 7, 8, 9, 10]}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = mergeSorted([5, 5, 5], [5, 5, 5])
        assert result == [5, 5, 5, 5, 5, 5], f"Test 8 failed: got {result}, expected {[5, 5, 5, 5, 5, 5]}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
