# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def SelectionSort(a):
2: ✓     n = len(a)
3: ✓     for i in range(n):
4: ✓         min_index = i
5: ✓         for j in range(i + 1, n):
6: ✓             if a[j] < a[min_index]:
7: ✓                 min_index = j
8: ✓         a[i], a[min_index] = a[min_index], a[i]
9: ✓     return a
```

## Complete Test File

```python
def SelectionSort(a):
    n = len(a)
    for i in range(n):
        min_index = i
        for j in range(i + 1, n):
            if a[j] < a[min_index]:
                min_index = j
        a[i], a[min_index] = a[min_index], a[i]
    return a

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = SelectionSort([3, 1, 2])
        assert result == [1, 2, 3], f"Test 1 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = SelectionSort([0])
        assert result == [0], f"Test 2 failed: got {result}, expected {[0]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = SelectionSort([5, 4, 3, 2, 1])
        assert result == [1, 2, 3, 4, 5], f"Test 3 failed: got {result}, expected {[1, 2, 3, 4, 5]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = SelectionSort([2, 2, 1, 4])
        assert result == [1, 2, 2, 4], f"Test 4 failed: got {result}, expected {[1, 2, 2, 4]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = SelectionSort([10, -5, 0, 3])
        assert result == [-5, 0, 3, 10], f"Test 5 failed: got {result}, expected {[-5, 0, 3, 10]}"
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
