# Coverage Report

Total executable lines: 12
Covered lines: 12
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def insertionSort(xs):
2: ✓     sorted_list = []
3: ✓     for x in xs:
4: ✓         inserted = False
5: ✓         for i in range(len(sorted_list)):
6: ✓             if x < sorted_list[i]:
7: ✓                 sorted_list.insert(i, x)
8: ✓                 inserted = True
9: ✓                 break
10: ✓         if not inserted:
11: ✓             sorted_list.append(x)
12: ✓     return sorted_list
```

## Complete Test File

```python
def insertionSort(xs):
    sorted_list = []
    for x in xs:
        inserted = False
        for i in range(len(sorted_list)):
            if x < sorted_list[i]:
                sorted_list.insert(i, x)
                inserted = True
                break
        if not inserted:
            sorted_list.append(x)
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
        result = insertionSort([42])
        assert result == [42], f"Test 2 failed: got {result}, expected {[42]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = insertionSort([3, 1, 4, 2])
        assert result == [1, 2, 3, 4], f"Test 3 failed: got {result}, expected {[1, 2, 3, 4]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = insertionSort([5, -1, 0, 10, -1])
        assert result == [-1, -1, 0, 5, 10], f"Test 4 failed: got {result}, expected {[-1, -1, 0, 5, 10]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = insertionSort([2, 2, 2, 2, 2])
        assert result == [2, 2, 2, 2, 2], f"Test 5 failed: got {result}, expected {[2, 2, 2, 2, 2]}"
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
