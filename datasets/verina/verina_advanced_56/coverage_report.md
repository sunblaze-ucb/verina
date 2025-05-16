# Coverage Report

Total executable lines: 4
Covered lines: 4
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def moveZeroes(xs):
2: ✓     non_zeroes = [x for x in xs if x != 0]
3: ✓     zeroes = [0] * (len(xs) - len(non_zeroes))
4: ✓     return non_zeroes + zeroes
```

## Complete Test File

```python
def moveZeroes(xs):
    non_zeroes = [x for x in xs if x != 0]
    zeroes = [0] * (len(xs) - len(non_zeroes))
    return non_zeroes + zeroes

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = moveZeroes([0, 1, 0, 3, 12])
        assert result == [1, 3, 12, 0, 0], f"Test 1 failed: got {result}, expected {[1, 3, 12, 0, 0]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = moveZeroes([0, 0, 1])
        assert result == [1, 0, 0], f"Test 2 failed: got {result}, expected {[1, 0, 0]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = moveZeroes([1, 2, 3])
        assert result == [1, 2, 3], f"Test 3 failed: got {result}, expected {[1, 2, 3]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = moveZeroes([0, 0, 0])
        assert result == [0, 0, 0], f"Test 4 failed: got {result}, expected {[0, 0, 0]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = moveZeroes([])
        assert result == [], f"Test 5 failed: got {result}, expected {[]}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = moveZeroes([4, 0, 5, 0, 6])
        assert result == [4, 5, 6, 0, 0], f"Test 6 failed: got {result}, expected {[4, 5, 6, 0, 0]}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = moveZeroes([0, 1])
        assert result == [1, 0], f"Test 7 failed: got {result}, expected {[1, 0]}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = moveZeroes([1, 0])
        assert result == [1, 0], f"Test 8 failed: got {result}, expected {[1, 0]}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    # Test case 9
    try:
        result = moveZeroes([2, 0, 0, 3])
        assert result == [2, 3, 0, 0], f"Test 9 failed: got {result}, expected {[2, 3, 0, 0]}"
        print(f"Test 9 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 9 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
