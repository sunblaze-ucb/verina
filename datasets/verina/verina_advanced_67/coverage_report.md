# Coverage Report

Total executable lines: 14
Covered lines: 14
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def runLengthEncode(s):
2: ✓     if not s:
3: ✓         return []
4: ✓     result = []
5: ✓     current = s[0]
6: ✓     count = 1
7: ✓     for char in s[1:]:
8: ✓         if char == current:
9: ✓             count += 1
10: ✓         else:
11: ✓             result.append((current, count))
12: ✓             current = char
13: ✓             count = 1
14: ✓     result.append((current, count))
15: ✓     return result
```

## Complete Test File

```python
def runLengthEncode(s):
    if not s:
        return []
    result = []
    current = s[0]
    count = 1
    for char in s[1:]:
        if char == current:
            count += 1
        else:
            result.append((current, count))
            current = char
            count = 1
    result.append((current, count))
    return result

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = runLengthEncode('')
        assert result == [], f"Test 1 failed: got {result}, expected {[]}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = runLengthEncode('aaa')
        assert result == [('a', 3)], f"Test 2 failed: got {result}, expected {[('a', 3)]}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = runLengthEncode('abbbcccaa')
        assert result == [('a', 1), ('b', 3), ('c', 3), ('a', 2)], f"Test 3 failed: got {result}, expected {[('a', 1), ('b', 3), ('c', 3), ('a', 2)]}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = runLengthEncode('xyz')
        assert result == [('x', 1), ('y', 1), ('z', 1)], f"Test 4 failed: got {result}, expected {[('x', 1), ('y', 1), ('z', 1)]}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = runLengthEncode('aabbaa')
        assert result == [('a', 2), ('b', 2), ('a', 2)], f"Test 5 failed: got {result}, expected {[('a', 2), ('b', 2), ('a', 2)]}"
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
