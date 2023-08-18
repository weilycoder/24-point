#include <iostream>
#include <stack>
#include <vector>
using namespace std;

typedef stack<int> st_int;
typedef vector<int> v_int;

const int goal = 24;
const char ops[4] = {'+', '-', '*', '/'};

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

inline int safe_div(int a, int b) {
	if (b == 0) return -2;
	if (a % b) return -1;
	return a / b;
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

char push_op(st_int &st, char op) {
	if (st.size() < 2) return -1;
	int a = st.top(), b;
	st.pop();
	b = st.top();
	st.pop();
	switch (op) {
		case 0:
			st.push(safe_add(a, b));
			break;
		case 1:
			st.push(safe_sub(a, b));
			break;
		case 2:
			st.push(safe_mul(a, b));
			break;
		case 3:
			st.push(safe_div(a, b));
			break;
		default:
			return -2;
	}
	if (st.top() < 0) return -3;
	return 0;
}

string dfs(v_int &data, st_int &st) {
	if (data.empty() && st.size() == 1 && st.top() == goal) return "";
	for (int i = 0; i < (int)data.size(); ++i) {
		if (data[i] < 0 || data[i] > 9) return "N/A";
		v_int tmp_v;
		st_int tmp_st = st;
		tmp_st.push(data[i]);
		for (int j = 0; j < (int)data.size(); ++j) {
			if (i == j) continue;
			tmp_v.push_back(data[j]);
		}
		string ans = dfs(tmp_v, tmp_st);
		if (ans != "N/A") return to_string(data[i]) + ans;
	}
	for (int i = 0; i < 4; ++i) {
		st_int tmp_st = st;
		if (push_op(tmp_st, i) == 0) {
			string ans = dfs(data, tmp_st);
			if (ans != "N/A") return ans.insert(0, 1, ops[i]);
		}
	}
	if (st.size()) {
		int tmp = factorial(st.top());
		if (tmp > 0) {
			st_int tmp_st = st;
			tmp_st.pop();
			tmp_st.push(tmp);
			string ans = dfs(data, tmp_st);
			if (ans != "N/A") return ans.insert(0, 1, '!');
		}
		tmp = isqrt_newton(st.top());
		if (tmp > 0) {
			st_int tmp_st = st;
			tmp_st.pop();
			tmp_st.push(tmp);
			string ans = dfs(data, tmp_st);
			if (ans != "N/A") return ans.insert(0, 1, 's');
		}
	}
	return "N/A";
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

void push_op(stack<string> &st, char op) {
	string a = st.top();
	st.pop();
	if (op == '!') {
		st.push(bracket_fac(a) + "!");
		return;
	} else if (op == 's') {
		st.push("sqrt(" + a + ")");
		return;
	}
	string b = st.top();
	st.pop();
	switch (op) {
		case '+':
			st.push(a + "+" + b);
			break;
		case '-':
			st.push(a + "-" + bracket_mul(b));
			break;
		case '*':
			st.push(bracket_mul(a) + "*" + bracket_mul(b));
			break;
		case '/':
			st.push(bracket_mul(a) + "/" + bracket_mul2(b));
			break;
	}
}

string solve(v_int &data) {
	st_int st;
	string ans = dfs(data, st);
	if (ans == "N/A") return ans;
	stack<string> tmp;
	for (int i = 0; i < (int)ans.length(); ++i) {
		if (ans[i] >= '0' && ans[i] <= '9') tmp.push(ans.substr(i, 1));
		else push_op(tmp, ans[i]);
	}
	return tmp.top();
}

string solve(v_int &data, int state) {
	STATE = state;
	return solve(data);
}

void solve(int a, int b, int c, int d) {
	v_int v;
	v.push_back(a);
	v.push_back(b);
	v.push_back(c);
	v.push_back(d);
	string ans = solve(v, 3);
	if (ans == "N/A") ans = solve(v, 2);
	if (ans == "N/A") ans = solve(v, 1);
	if (ans == "N/A") ans = solve(v, 0);
	cout << a << b << c << d << " " << ans << endl; 
}

int main() {
	for (int a = 0; a < 10; ++a)
		for (int b = a; b < 10; ++b)
			for (int c = b; c < 10; ++c)
				for (int d = c; d < 10; ++d)
					solve(a, b, c, d);
	return 0;
}
