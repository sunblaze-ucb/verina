# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def SwapSimultaneous(X, Y):
2: ✓     return (Y, X)
```

## Complete Test File

```python
def SwapSimultaneous(X, Y):
    return (Y, X)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = SwapSimultaneous(3, 4)
        assert result == '(4, 3)', f"Test 1 failed: got {result}, expected {'(4, 3)'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = SwapSimultaneous(-10, 20)
        assert result == '(20, -10)', f"Test 2 failed: got {result}, expected {'(20, -10)'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = SwapSimultaneous(0, 0)
        assert result == '(0, 0)', f"Test 3 failed: got {result}, expected {'(0, 0)'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = SwapSimultaneous(123, -456)
        assert result == '(-456, 123)', f"Test 4 failed: got {result}, expected {'(-456, 123)'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = SwapSimultaneous(-1, -2)
        assert result == '(-2, -1)', f"Test 5 failed: got {result}, expected {'(-2, -1)'}"
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
