# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def uniqueProduct(arr):
2: ✓     unique_numbers = set(arr)
3: ✓     product = 1
4: ✓     for number in unique_numbers:
5: ✓         product *= number
6: ✓     return product
```

## Complete Test File

```python
def uniqueProduct(arr):
    unique_numbers = set(arr)
    product = 1
    for number in unique_numbers:
        product *= number
    return product

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = uniqueProduct([2, 3, 2, 4])
        assert result == 24, f"Test 1 failed: got {result}, expected {24}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = uniqueProduct([5, 5, 5, 5])
        assert result == 5, f"Test 2 failed: got {result}, expected {5}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = uniqueProduct([])
        assert result == 1, f"Test 3 failed: got {result}, expected {1}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = uniqueProduct([1, 2, 3])
        assert result == 6, f"Test 4 failed: got {result}, expected {6}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = uniqueProduct([0, 2, 3])
        assert result == 0, f"Test 5 failed: got {result}, expected {0}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = uniqueProduct([-1, -2, -1, -3])
        assert result == -6, f"Test 6 failed: got {result}, expected {-6}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = uniqueProduct([10, 10, 20, 20, 30])
        assert result == 6000, f"Test 7 failed: got {result}, expected {6000}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
