# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def modify_array_element(arr, index1, index2, val):
2: ✓     new_arr = arr.copy()
3: ✓     modified_inner = new_arr[index1][:]
4: ✓     modified_inner[index2] = val
5: ✓     new_arr[index1] = modified_inner
6: ✓     return new_arr
```

## Complete Test File

```python
def modify_array_element(arr, index1, index2, val):
    new_arr = arr.copy()
    modified_inner = new_arr[index1][:]
    modified_inner[index2] = val
    new_arr[index1] = modified_inner
    return new_arr

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = modify_array_element([[1, 2, 3], [4, 5, 6]], 0, 1, 99)
        assert result == [[1, 99, 3], [4, 5, 6]], f"Test 1 failed: got {result}, expected {[[1, 99, 3], [4, 5, 6]]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = modify_array_element([[7, 8], [9, 10]], 1, 0, 0)
        assert result == [[7, 8], [0, 10]], f"Test 2 failed: got {result}, expected {[[7, 8], [0, 10]]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = modify_array_element([[0, 0, 0]], 0, 2, 5)
        assert result == [[0, 0, 5]], f"Test 3 failed: got {result}, expected {[[0, 0, 5]]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = modify_array_element([[3, 4, 5], [6, 7, 8], [9, 10, 11]], 2, 1, 100)
        assert result == [[3, 4, 5], [6, 7, 8], [9, 100, 11]], f"Test 4 failed: got {result}, expected {[[3, 4, 5], [6, 7, 8], [9, 100, 11]]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = modify_array_element([[1]], 0, 0, 42)
        assert result == [[42]], f"Test 5 failed: got {result}, expected {[[42]]}"
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
