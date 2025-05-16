# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def cubeElements(a):
2: ✓     return [x * x * x for x in a]
```

## Complete Test File

```python
def cubeElements(a):
    return [x * x * x for x in a]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = cubeElements([1, 2, 3, 4])
        assert result == [1, 8, 27, 64], f"Test 1 failed: got {result}, expected {[1, 8, 27, 64]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = cubeElements([0, -1, -2, 3])
        assert result == [0, -1, -8, 27], f"Test 2 failed: got {result}, expected {[0, -1, -8, 27]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = cubeElements([])
        assert result == [], f"Test 3 failed: got {result}, expected {[]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = cubeElements([5])
        assert result == [125], f"Test 4 failed: got {result}, expected {[125]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = cubeElements([-3, -3])
        assert result == [-27, -27], f"Test 5 failed: got {result}, expected {[-27, -27]}"
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
