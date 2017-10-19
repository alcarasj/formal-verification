method isPrefix(pre: seq<char>, str: seq<char>) returns (res: bool)
	requires |pre| > 0 && |str| >= |pre|
{
	var i := 0;
	while i < |pre|
		invariant i >= 0
		{
			if pre[i] == str[i]	
			{ 
				res := true; 
			}
			else 
			{
				return false;
			}
			i := i + 1;
		}
}

method isSubString(sub: seq<char>, str: seq<char>) returns (res: bool)
	requires |sub| > 0 && |str| >= |sub|
{
	var isPrefix := isPrefix(sub, str);
	if isPrefix
	{
		return true;
	}
	res := false;
	var i := 0;
	var j := 0;
	while i < |str|
		invariant i >= 0
	{
		if j < |sub|
		{
			if str[i] == sub[j] {
				j := j + 1;
			}
		}
		else
		{
			j := 0;
		}
		if j == |sub| 
		{
			return true;
		}
		i := i + 1;
	}
}

method haveCommonKSubstring(k: nat, str1: seq<char>, str2: seq<char>) returns (found: bool)
	requires |str1| > 0 && |str2| > 0
{
	var biggerString;
	var smallerString;
	if |str1| > |str2|
	{
		var isStr2ASubStringOfStr1 := isSubString(str2, str1);
		if isStr2ASubStringOfStr1
		{
			return true;
		}
		biggerString := str1;
		smallerString := str2;
	}
	else
	{	
		var isStr1ASubStringOfStr2 := isSubString(str1, str2);
		if isStr1ASubStringOfStr2
		{
			return true;
		}
		biggerString := str2;
		smallerString := str1;
	}
	var i := 0;
	var j := 0;
	var matches := 0;
	var foundMatch := false;
	while i < |smallerString|
		invariant i >= 0
	{
		if !foundMatch
		{
			while j < |biggerString|
				invariant j >= 0
			{
				if smallerString[i] == biggerString[j]
				{
					matches := matches + 1;
					foundMatch := true;
				}
				j := j + 1;
			}
		}
		else
		{
			if j + 1 >= |biggerString|
			{
				foundMatch := false;
			}
			else
			{
				j := j + 1;
				if smallerString[i] == biggerString[j]
				{
					matches := matches + 1;
				}
				else
				{
					foundMatch := false;
					matches := 0;
				}
			}
		}
		if matches == k
		{
			return true;
		}
		i := i + 1;
	}
	return false;
}

method maxCommonSubstringLength(str1: seq<char>, str2: seq<char>) returns (len: nat)
	requires |str1| > 0 && |str2| > 0
{
	
}