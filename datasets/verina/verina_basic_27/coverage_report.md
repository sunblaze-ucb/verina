# Coverage Report

Total executable lines: 5
Covered lines: 5
Missed lines: 0
Coverage percentage: 100.00%

## Source Code with Coverage

```python
1: ✓ def findFirstRepeatedChar(str1):
2: ✓   for index,c in enumerate(str1):
3: ✓     if str1[:index+1].count(c) > 1:
4: ✓       return c 
5: ✓   return "None"
```

## Complete Test File

```python
def findFirstRepeatedChar(str1):
  for index,c in enumerate(str1):
    if str1[:index+1].count(c) > 1:
      return c 
  return "None"

def run_tests():
    test_results = []
    # Test case 1
    try:
        result = findFirstRepeatedChar('abca')
        assert result == {'found': True, 'char': 'a'}, f"Test 1 failed: got {result}, expected {{'found': True, 'char': 'a'}}"
        print(f"Test 1 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 1 failed: {e}")
        test_results.append(False)

    # Test case 2
    try:
        result = findFirstRepeatedChar('abcdef')
        assert result == {'found': False, 'char': '\x00'}, f"Test 2 failed: got {result}, expected {{'found': False, 'char': '\x00'}}"
        print(f"Test 2 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 2 failed: {e}")
        test_results.append(False)

    # Test case 3
    try:
        result = findFirstRepeatedChar('aabbcc')
        assert result == {'found': True, 'char': 'a'}, f"Test 3 failed: got {result}, expected {{'found': True, 'char': 'a'}}"
        print(f"Test 3 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 3 failed: {e}")
        test_results.append(False)

    # Test case 4
    try:
        result = findFirstRepeatedChar('')
        assert result == {'found': False, 'char': '\x00'}, f"Test 4 failed: got {result}, expected {{'found': False, 'char': '\x00'}}"
        print(f"Test 4 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 4 failed: {e}")
        test_results.append(False)

    # Test case 5
    try:
        result = findFirstRepeatedChar('abbc')
        assert result == {'found': True, 'char': 'b'}, f"Test 5 failed: got {result}, expected {{'found': True, 'char': 'b'}}"
        print(f"Test 5 passed")
        test_results.append(True)
    except Exception as e:
        print(f"Test 5 failed: {e}")
        test_results.append(False)

    # Test case 6
    try:
        result = findFirstRepeatedChar('Aa')
        assert result == {'found': False, 'char': '\x00'}, f"Test 6 failed: got {result}, expected {{'found': False, 'char': '\x00'}}"
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
