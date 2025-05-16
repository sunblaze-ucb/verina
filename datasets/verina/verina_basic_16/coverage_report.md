# Coverage Report

Total executable lines: 2
Covered lines: 2
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def replaceChars(s, oldChar, newChar):
2: ✓     return ''.join(newChar if ch == oldChar else ch for ch in s)
```

## Complete Test File

```python
def replaceChars(s, oldChar, newChar):
    return ''.join(newChar if ch == oldChar else ch for ch in s)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = replaceChars('hello, world!', ',', ';')
        assert result == 'hello; world!', f"Test 1 failed: got {result}, expected {'hello; world!'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = replaceChars('a,b.c', ',', ':')
        assert result == 'a:b.c', f"Test 2 failed: got {result}, expected {'a:b.c'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = replaceChars('hello, world!', 'o', 'O')
        assert result == 'hellO, wOrld!', f"Test 3 failed: got {result}, expected {'hellO, wOrld!'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = replaceChars('', 'x', 'y')
        assert result == '', f"Test 4 failed: got {result}, expected {''}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = replaceChars('test', 'x', 'y')
        assert result == 'test', f"Test 5 failed: got {result}, expected {'test'}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = replaceChars('unchanged', 'u', 'u')
        assert result == 'unchanged', f"Test 6 failed: got {result}, expected {'unchanged'}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = replaceChars('aaa', 'a', 'b')
        assert result == 'bbb', f"Test 7 failed: got {result}, expected {'bbb'}"
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
