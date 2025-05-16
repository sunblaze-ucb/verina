# Coverage Report

Total executable lines: 16
Covered lines: 16
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def runLengthEncoder(input):
2: ✓     if not input:
3: ✓         return ""
4: ✓     encoded = []
5: ✓     count = 1
6: ✓     current = input[0]
7: ✓     for char in input[1:]:
8: ✓         if char == current:
9: ✓             count += 1
10: ✓         else:
11: ✓             encoded.append(current)
12: ✓             encoded.append(str(count))
13: ✓             current = char
14: ✓             count = 1
15: ✓     encoded.append(current)
16: ✓     encoded.append(str(count))
17: ✓     return "".join(encoded)
```

## Complete Test File

```python
def runLengthEncoder(input):
    if not input:
        return ""
    encoded = []
    count = 1
    current = input[0]
    for char in input[1:]:
        if char == current:
            count += 1
        else:
            encoded.append(current)
            encoded.append(str(count))
            current = char
            count = 1
    encoded.append(current)
    encoded.append(str(count))
    return "".join(encoded)

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = runLengthEncoder('aaabbbcc')
        assert result == 'a3b3c2', f"Test 1 failed: got {result}, expected {'a3b3c2'}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = runLengthEncoder('!!!$$$%%%')
        assert result == '!3$3%3', f"Test 2 failed: got {result}, expected {'!3$3%3'}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = runLengthEncoder('aaaaa')
        assert result == 'a5', f"Test 3 failed: got {result}, expected {'a5'}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = runLengthEncoder('abcd')
        assert result == 'a1b1c1d1', f"Test 4 failed: got {result}, expected {'a1b1c1d1'}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = runLengthEncoder('')
        assert result == '', f"Test 5 failed: got {result}, expected {''}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = runLengthEncoder('AaABb')
        assert result == 'A1a1A1B1b1', f"Test 6 failed: got {result}, expected {'A1a1A1B1b1'}"
        print(f"Test 6 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 6 failed: {e}")
        test_results.append(False)

    # Test case 7
    try:
        result = runLengthEncoder('wwwwwwwwwwwwwwwww')
        assert result == 'w17', f"Test 7 failed: got {result}, expected {'w17'}"
        print(f"Test 7 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 7 failed: {e}")
        test_results.append(False)

    # Test case 8
    try:
        result = runLengthEncoder('a')
        assert result == 'a1', f"Test 8 failed: got {result}, expected {'a1'}"
        print(f"Test 8 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 8 failed: {e}")
        test_results.append(False)

    # Test case 9
    try:
        result = runLengthEncoder('  ')
        assert result == ' 2', f"Test 9 failed: got {result}, expected {' 2'}"
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
