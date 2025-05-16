# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def toUppercase(s):
2: ✓     return s.upper()
```

## Complete Test File

```python
def toUppercase(s):
    return s.upper()

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = toUppercase('Hello, World!')
        assert result == 'HELLO, WORLD!', f"Test 1 failed: got {result}, expected {'HELLO, WORLD!'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = toUppercase('abc')
        assert result == 'ABC', f"Test 2 failed: got {result}, expected {'ABC'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = toUppercase('ABC')
        assert result == 'ABC', f"Test 3 failed: got {result}, expected {'ABC'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = toUppercase('123!?@')
        assert result == '123!?@', f"Test 4 failed: got {result}, expected {'123!?@'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = toUppercase('')
        assert result == '', f"Test 5 failed: got {result}, expected {''}"
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
