# Coverage Report

Total executable lines: 6
Covered lines: 6
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def minArray(a):
2: ✓     def helper(i, current_min):
3: ✓         if i == len(a):
4: ✓             return current_min
5: ✓         return helper(i + 1, a[i] if a[i] < current_min else current_min)
6: ✓     return helper(1, a[0])
```

## Complete Test File

```python
def minArray(a):
    def helper(i, current_min):
        if i == len(a):
            return current_min
        return helper(i + 1, a[i] if a[i] < current_min else current_min)
    return helper(1, a[0])

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = minArray([5, 3, 8, 2, 7])
        assert result == '2', f"Test 1 failed: got {result}, expected {'2'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = minArray([10, 10, 10])
        assert result == '10', f"Test 2 failed: got {result}, expected {'10'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = minArray([-1, -5, 3, 0])
        assert result == '-5', f"Test 3 failed: got {result}, expected {'-5'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = minArray([42])
        assert result == '42', f"Test 4 failed: got {result}, expected {'42'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = minArray([3, -2, 0, -2, 5])
        assert result == '-2', f"Test 5 failed: got {result}, expected {'-2'}"
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
