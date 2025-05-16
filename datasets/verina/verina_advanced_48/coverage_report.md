# Coverage Report

Total executable lines: 19
Covered lines: 19
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def mergeSort(lst):
2: ✓     if len(lst) <= 1:
3: ✓         return lst
4: ✓     mid = len(lst) // 2
5: ✓     left = mergeSort(lst[:mid])
6: ✓     right = mergeSort(lst[mid:])
7: ✓     return merge(left, right)
8: ✓ 
9: ✓ def merge(left, right):
10: ✓     result = []
11: ✓     i, j = 0, 0
12: ✓     while i < len(left) and j < len(right):
13: ✓         if left[i] < right[j]:
14: ✓             result.append(left[i])
15: ✓             i += 1
16: ✓         else:
17: ✓             result.append(right[j])
18: ✓             j += 1
19: ✓     result.extend(left[i:])
20: ✓     result.extend(right[j:])
21: ✓     return result
```

## Complete Test File

```python
def mergeSort(lst):
    if len(lst) <= 1:
        return lst
    mid = len(lst) // 2
    left = mergeSort(lst[:mid])
    right = mergeSort(lst[mid:])
    return merge(left, right)

def merge(left, right):
    result = []
    i, j = 0, 0
    while i < len(left) and j < len(right):
        if left[i] < right[j]:
            result.append(left[i])
            i += 1
        else:
            result.append(right[j])
            j += 1
    result.extend(left[i:])
    result.extend(right[j:])
    return result

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = mergeSort([5, 2, 9, 1, 5, 6])
        assert result == [1, 2, 5, 5, 6, 9], f"Test 1 failed: got {result}, expected {[1, 2, 5, 5, 6, 9]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = mergeSort([3, 1, 4, 1, 5, 9, 2, 6])
        assert result == [1, 1, 2, 3, 4, 5, 6, 9], f"Test 2 failed: got {result}, expected {[1, 1, 2, 3, 4, 5, 6, 9]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = mergeSort([])
        assert result == [], f"Test 3 failed: got {result}, expected {[]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = mergeSort([1])
        assert result == [1], f"Test 4 failed: got {result}, expected {[1]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = mergeSort([5, 5, 5, 5])
        assert result == [5, 5, 5, 5], f"Test 5 failed: got {result}, expected {[5, 5, 5, 5]}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = mergeSort([9, 8, 7, 6, 5, 4, 3, 2, 1])
        assert result == [1, 2, 3, 4, 5, 6, 7, 8, 9], f"Test 6 failed: got {result}, expected {[1, 2, 3, 4, 5, 6, 7, 8, 9]}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = mergeSort([1, 2, 3, 4, 5])
        assert result == [1, 2, 3, 4, 5], f"Test 7 failed: got {result}, expected {[1, 2, 3, 4, 5]}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = mergeSort([-3, -1, -5, -2])
        assert result == [-5, -3, -2, -1], f"Test 8 failed: got {result}, expected {[-5, -3, -2, -1]}"
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
