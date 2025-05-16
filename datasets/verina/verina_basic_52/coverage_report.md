# Coverage Report

Total executable lines: 9
Covered lines: 9
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def BubbleSort(a):
2: ✓     def swap(arr, i, j):
3: ✓         arr[i], arr[j] = arr[j], arr[i]
4: ✓     n = len(a)
5: ✓     for i in range(n):
6: ✓         for j in range(0, n - i - 1):
7: ✓             if a[j] > a[j + 1]:
8: ✓                 swap(a, j, j + 1)
9: ✓     return a
```

## Complete Test File

```python
def BubbleSort(a):
    def swap(arr, i, j):
        arr[i], arr[j] = arr[j], arr[i]
    n = len(a)
    for i in range(n):
        for j in range(0, n - i - 1):
            if a[j] > a[j + 1]:
                swap(a, j, j + 1)
    return a

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = BubbleSort([5, 4, 3, 2, 1])
        assert result == [1, 2, 3, 4, 5], f"Test 1 failed: got {result}, expected {[1, 2, 3, 4, 5]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = BubbleSort([1, 2, 3, 4, 5])
        assert result == [1, 2, 3, 4, 5], f"Test 2 failed: got {result}, expected {[1, 2, 3, 4, 5]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = BubbleSort([3, 1, 2, 1, 5])
        assert result == [1, 1, 2, 3, 5], f"Test 3 failed: got {result}, expected {[1, 1, 2, 3, 5]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = BubbleSort([10])
        assert result == [10], f"Test 4 failed: got {result}, expected {[10]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = BubbleSort([4, 4, 4, 2, 2, 8])
        assert result == [2, 2, 4, 4, 4, 8], f"Test 5 failed: got {result}, expected {[2, 2, 4, 4, 4, 8]}"
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
