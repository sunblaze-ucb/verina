# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def reverseString(s):
2: ✓     return s[::-1]
```

## Complete Test File

```python
def reverseString(s):
    return s[::-1]

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = reverseString('hello')
        assert result == 'olleh', f"Test 1 failed: got {result}, expected {'olleh'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = reverseString('a')
        assert result == 'a', f"Test 2 failed: got {result}, expected {'a'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = reverseString('')
        assert result == '', f"Test 3 failed: got {result}, expected {''}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = reverseString('racecar')
        assert result == 'racecar', f"Test 4 failed: got {result}, expected {'racecar'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = reverseString('Lean')
        assert result == 'naeL', f"Test 5 failed: got {result}, expected {'naeL'}"
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
