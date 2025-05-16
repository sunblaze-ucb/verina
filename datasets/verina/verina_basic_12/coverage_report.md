# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def cubeSurfaceArea(size):
2: ✓     return 6 * (size ** 2)
```

## Complete Test File

```python
def cubeSurfaceArea(size):
    return 6 * (size ** 2)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = cubeSurfaceArea(3)
        assert result == 54, f"Test 1 failed: got {result}, expected {54}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = cubeSurfaceArea(1)
        assert result == 6, f"Test 2 failed: got {result}, expected {6}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = cubeSurfaceArea(10)
        assert result == 600, f"Test 3 failed: got {result}, expected {600}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = cubeSurfaceArea(5)
        assert result == 150, f"Test 4 failed: got {result}, expected {150}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = cubeSurfaceArea(2)
        assert result == 24, f"Test 5 failed: got {result}, expected {24}"
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
