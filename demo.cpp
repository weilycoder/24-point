// twenty-four-point
#include <cstring>
#include <iostream>
#include <vector>
using namespace std;

typedef vector<int> v_int;

short STATE = 0;

inline int safe_add(int a, int b) {
	long long x = (long long)(a) + b;
	if (x > INT_MAX || x < 0) return -1;
	return x;
}

inline int safe_sub(int a, int b) {
	long long x = (long long)(a) - b;
	if (x > INT_MAX || x < 0) return -1;
	return x;
}

inline int safe_mul(int a, int b) {
	long long x = (long long)(a) * b;
	if (x > INT_MAX || x < 0) return -1;
	return x;
}

int factorial(int x) {
	if (STATE & 1) return -5;
	if (x < 0) return -1;
	if (x == 1 || x == 2) return -3;
	long long ans = 1LL;
	for (int i = 2; i <= x; ++i) {
		ans *= i;
		if (ans > INT_MAX) return -2;
	}
	return ans;
}

int unfactorial(int x) {
	if (STATE & 1) return -5;
	if (x < 1) return -1;
	int i = 1;
	for (; !(x % i); ++i) x /= i;
	if (x == 1) return i - 1;
	else return -1;
}

int square(int x) {
	if (STATE & 2) return -5;
	if (x < 65535) return x * x;
	return -1;
}

int isqrt_newton(int n) {
	if (STATE & 2) return -5;
	if (n < 0) return -1;
	if (n < 2) return -2;
	int x = 1;
	bool decreased = false;
	for (;;) {
		int nx = (x + n / x) >> 1;
		if (x == nx || (nx > x && decreased)) break;
		decreased = nx < x;
		x = nx;
	}
	if (x * x != n) return -3;
	return x;
}

string join(v_int &x) {
	string ans;
	for (int i = 0; i < (int)x.size(); ++i)
		ans.append(to_string(x[i])).append(1, '+');
	ans.pop_back();
	return ans;
}

inline string _bracket(string a) {
	return "(" + a + ")";
}

string bracket(string a, string ops) {
	int flag = 0;
	for (int i = 0; i < (int)a.length(); ++i) {
		if (a[i] == '(') flag++;
		else if (a[i] == ')') flag--;
		if (!flag && (ops.find(a[i]) != string::npos))
			return _bracket(a);
	}
	return a;
}

inline string bracket_mul(string a) {
	return bracket(a, "+-");
}
inline string bracket_mul2(string a) {
	return bracket(a, "+-*/");
}
inline string bracket_fac(string a) {
	return bracket(a, "+-*/!");
}

string solve(v_int &, int);
string dfs(v_int &, int, string, int);

string dfs_add(v_int &nums, int x, string t, int goal) {
    if (x < 0) return "N/A";
	string ans;
flag_sqrt_dfs_add:
	int cx = x;
	string ct = t;
flag_fac_dfs_add:
	ans = solve(nums, safe_sub(goal, x));
	if (ans != "N/A") return ans + "+" + t;
	ans = solve(nums, safe_add(goal, x));
	if (ans != "N/A") return ans + "-" + t;
	x = factorial(x);
	if (x > 0) {
		t = bracket_fac(t) + "!";
		goto flag_fac_dfs_add;
	}
	x = cx, t = ct;
	x = isqrt_newton(x);
	if (x > 1) {
		t = "sqrt(" + t + ")";
		goto flag_sqrt_dfs_add;
	}
	return "N/A";
}

string dfs_mul(v_int &nums, int x, string t, int goal) {
    if (x < 0) return "N/A";
	string ans;
flag_sqrt_dfs_add:
	int cx = x;
	string ct = t;
flag_fac_dfs_mul:
	if (x != 0) {
		if (goal % x == 0) {
			ans = solve(nums, goal / x);
			if (ans != "N/A") return bracket_mul(ans) + "*" + t;
		}
		ans = solve(nums, safe_mul(goal, x));
		if (ans != "N/A") return bracket_mul(ans) + "/" + t;
		if (goal != 0 && x % goal == 0) {
			ans = solve(nums, x / goal);
			if (ans != "N/A") return t + "/" + bracket_mul2(ans);
		}
	} else if (goal == 0) {
		ans = join(nums);
		return bracket_mul(ans) + "*0";
	}
	x = factorial(x);
	if (x > 0) {
		t = bracket_fac(t) + "!";
		goto flag_fac_dfs_mul;
	}
	x = cx, t = ct;
	x = isqrt_newton(x);
	if (x > 0) {
		t = "sqrt(" + t + ")";
		goto flag_sqrt_dfs_add;
	}
	return "N/A";
}

string ddfs(v_int &nums, int x, string t, int goal) {
	string ans;
	if (nums.size() < 2) return "N/A";
	for (int i = 0; i < (int)nums.size(); ++i) {
		v_int tmp;
		for (int j = 0; j < (int)nums.size(); ++j) {
			if (i == j) continue;
			tmp.push_back(nums[j]);
		}
		ans = dfs_mul(tmp, safe_add(x, nums[i]), _bracket(t + "+" + to_string(nums[i])), goal);
		if (ans != "N/A") return ans;
		ans = dfs_mul(tmp, safe_sub(x, nums[i]), _bracket(t + "-" + to_string(nums[i])), goal);
		if (ans != "N/A") return ans;
		ans = dfs_add(tmp, safe_mul(x, nums[i]), t + "*" + to_string(nums[i]), goal);
		if (ans != "N/A") return ans;
	}
	return "N/A";
}

string dfs(v_int &nums, int x, string t, int goal) {
	string ans;
	ans = dfs_add(nums, x, t, goal);
	if (ans != "N/A") return ans;
	ans = dfs_mul(nums, x, t, goal);
	if (ans != "N/A") return ans;
	ans = ddfs(nums, x, t, goal);
	return "N/A";
}

string solve(v_int &nums, int goal = 24) {
	if (nums.size() == 0 || goal < 0) return "N/A";
	if (nums.size() == 1) {
		if (nums[0] == goal)
			return to_string(goal);
	} else {
		string ans;
		for (int i = 0; i < (int)nums.size(); ++i) {
			v_int tmp;
			if (nums[i] < 0) return "N/A";
			for (int j = 0; j < (int)nums.size(); ++j) {
				if (i == j) continue;
				tmp.push_back(nums[j]);
			}
			ans = dfs(tmp, nums[i], to_string(nums[i]), goal);
			if (ans != "N/A") return ans;
		}
	}
	int uf = unfactorial(goal);
	if (uf == 1) uf = 0;
	if (uf > 2 || uf == 0) {
		string ans = solve(nums, uf);
		if (ans != "N/A") return bracket_fac(ans) + "!";
	}
	int isq = square(goal);
	if (isq > goal) {
		string ans = solve(nums, isq);
		if (ans != "N/A") return "sqrt(" + ans + ")";
	}
	return "N/A";
}

int read(const char *str) {
	int x = 0;
	if (str[0] == 0) return -1;
	for (int i = 0; str[i]; ++i) {
		if (str[i] >= '0' && str[i] <= '9') x = x * 10 + (str[i] ^ '0');
		else return -1;
	}
	return x;
}

int main(int argc, char *argv[]) {
	int t;
	v_int v;
	for (int i = 1; i < argc; ++i) {
		if (strcmp(argv[i], "-f") == 0)
			STATE |= 1;
		else if (strcmp(argv[i], "-s") == 0)
			STATE |= 2;
		else if (strcmp(argv[i], "-d") == 0) {
			int j = i + 1;
			for (; j < argc; ++j) {
				t = read(argv[j]);
				if (t < 0) break;
				v.push_back(t);
			}
			i = j - 1;
		} else {
			STATE = 0;
			v.clear();
			break;
		}
	}
	if (!v.size()) while (cin >> t) v.push_back(t);
	cout << solve(v);
	return 0;
}
