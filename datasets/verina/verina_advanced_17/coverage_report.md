# Coverage Report

Total executable lines: 10
Covered lines: 10
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def insertionSort(l):
2: ✓     sorted_list = l[:]
3: ✓     for i in range(1, len(sorted_list)):
4: ✓         key = sorted_list[i]
5: ✓         j = i - 1
6: ✓         while j >= 0 and sorted_list[j] > key:
7: ✓             sorted_list[j + 1] = sorted_list[j]
8: ✓             j -= 1
9: ✓         sorted_list[j + 1] = key
10: ✓     return sorted_list
```

## Complete Test File

```python
def insertionSort(l):
    sorted_list = l[:]
    for i in range(1, len(sorted_list)):
        key = sorted_list[i]
        j = i - 1
        while j >= 0 and sorted_list[j] > key:
            sorted_list[j + 1] = sorted_list[j]
            j -= 1
        sorted_list[j + 1] = key
    return sorted_list

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = insertionSort([])
        assert result == [], f"Test 1 failed: got {result}, expected {[]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = insertionSort([5])
        assert result == [5], f"Test 2 failed: got {result}, expected {[5]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = insertionSort([1, 2, 3])
        assert result == [1, 2, 3], f"Test 3 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = insertionSort([3, 2, 1])
        assert result == [1, 2, 3], f"Test 4 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = insertionSort([4, 2, 2, 3])
        assert result == [2, 2, 3, 4], f"Test 5 failed: got {result}, expected {[2, 2, 3, 4]}"
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
