# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def toLowercase(s):
2: ✓     return s.lower()
```

## Complete Test File

```python
def toLowercase(s):
    return s.lower()

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = toLowercase('Hello, World!')
        assert result == 'hello, world!', f"Test 1 failed: got {result}, expected {'hello, world!'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = toLowercase('ABC')
        assert result == 'abc', f"Test 2 failed: got {result}, expected {'abc'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = toLowercase('abc')
        assert result == 'abc', f"Test 3 failed: got {result}, expected {'abc'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = toLowercase('')
        assert result == '', f"Test 4 failed: got {result}, expected {''}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = toLowercase('1234!@')
        assert result == '1234!@', f"Test 5 failed: got {result}, expected {'1234!@'}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = toLowercase('MixedCASE123')
        assert result == 'mixedcase123', f"Test 6 failed: got {result}, expected {'mixedcase123'}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    return test_results

if __name__ == '__main__':
    results = run_tests()
    print(f"\n{sum(results)}/{len(results)} tests passed")

```
