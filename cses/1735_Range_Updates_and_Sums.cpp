#include <iostream>
#include <cstdio>
#include <cstdlib>
#include <algorithm>
#include <cmath>
#include <vector>
#include <set>
#include <map>
#include <unordered_set>
#include <unordered_map>
#include <queue>
#include <ctime>
#include <cassert>
#include <complex>
#include <string>
#include <cstring>
#include <chrono>
#include <random>
#include <queue>
#include <bitset>
using namespace std;

typedef long long ll;
typedef long long unsigned int llui;
typedef pair<int,int> ii;
typedef pair<ll,ll> pll;
typedef vector<ii> vii;
typedef vector<int> vi;
typedef vector<ll> vl;
typedef vector< vector<int> > vvi;
typedef vector< vector<ll> > vvl;
typedef set<int> si;
typedef map<string, int> msi;
typedef map<int, int> mii;

#define INF 1000000000
#define MOD 1000000007
#define EPS 1e-9
#define ALL(x) (x).begin(), (x).end()
#define RALL(x) (x).rbegin(), (x).rend()
#define SORT(x) sort((x).begin(),(x).end())
#define UNIQUE(x) SORT(x),(x).erase(unique((x).begin(),(x).end()),(x).end())
#define F first
#define S second
#define MP make_pair
#define PB push_back
#define EB emplace_back
#define LB lower_bound
#define UB upper_bound
#define SZ(a) int((a).size())
#define CLR(a) memset(a,0,sizeof(a))
#define SET(a,b) memset(a,b,sizeof(a))
#define POSL(x,v) (lower_bound(x.begin(),x.end(),v)-x.begin())
#define POSU(x,v) (upper_bound(x.begin(),x.end(),v)-x.begin())

#define FOR(i,a,b) for (int i = int(a); i < int(b); i++)
#define FORD(i,a,b) for(int i=int(b)-1; i>=int(a); i--)
#define REP(i, n) for (int i = 0; i < int(n); i++)
#define REP1(i,n) for (int i = 1; i <= int(n); i++)
#define REV(i, n) for (int i = int(n)-1; i >=0 ; i--)

#define sd(n) scanf("%d",&n)
#define dsd(n) int n; scanf("%d",&n)
#define sd2(a,b) scanf("%d%d",&a,&b)
#define dsd2(a,b) int a,b; scanf("%d%d",&a,&b)
#define sd3(a,b,c) scanf("%d%d%d",&a,&b,&c)
#define dsd3(a,b,c) int a,b,c; scanf("%d%d%d",&a,&b,&c)
#define pd(n) printf("%d\n",n)
#define pds(n) printf("%d ",n)
#define sl(n) scanf("%lld",&n)
#define dsl(n) ll n; scanf("%lld",&n)
#define sl2(a,b) scanf("%lld%lld",&a,&b)
#define dsl2(a,b) ll a,b; scanf("%lld%lld",&a,&b)
#define sl3(a,b,c) scanf("%lld%lld%lld",&a,&b,&c)
#define dsl3(a,b,c) ll a,b,c; scanf("%lld%lld%lld",&a,&b,&c)
#define pl(n) printf("%lld\n",n)	
#define pls(n) printf("%lld ",n)	
#define PR(a,n) { REP(_,n) cout<<a[_]<<' '; cout<<"\n"; }
#define PR1(a,n) { REP1(_,n) cout<<a[_]<<' '; cout<<"\n"; }
#define trace(x) cerr << " [" << #x << ": " << x << "]\n"

#define sim template < class c
#define ris return * this
#define dor > debug & operator <<
#define eni(x) sim > typename \
  enable_if<sizeof dud<c>(0) x 1, debug&>::type operator<<(c i) {
sim > struct rge { c b, e; };
sim > rge<c> range(c i, c j) { return rge<c>{i, j}; }
sim > auto dud(c* x) -> decltype(cerr << *x, 0);
sim > char dud(...);
struct debug {
#ifdef LOCAL
~debug() { cerr << endl; }
eni(!=) cerr << boolalpha << i; ris; }
eni(==) ris << range(begin(i), end(i)); }
sim, class b dor(pair < b, c > d) {
  ris << "(" << d.first << ", " << d.second << ")";
}
sim dor(rge<c> d) {
  *this << "[";
  for (auto it = d.b; it != d.e; ++it)
    *this << ", " + 2 * (it == d.b) << *it;
  ris << "]";
}
#else
sim dor(const c&) { ris; }
#endif
};
#define imie(...) " [" << #__VA_ARGS__ ": " << (__VA_ARGS__) << "] "

inline int two(int n) { return 1 << n; }
inline int test(int n, int b) { return (n>>b)&1; }
inline void set_bit(int & n, int b) { n |= two(b); }
inline void unset_bit(int & n, int b) { n &= ~two(b); }
inline int last_bit(int n) { return n & (-n); }
inline int ones(int n) { int res = 0; while(n && ++res) n-=n&(-n); return res; }

#define LSOne(S) (S&(-S))

const double pi = acos(-1);
//const int oo = 0x3f3f3f3f;

int cmp(double x, double y = 0, double tol = EPS) {
    return (x <= y + tol) ? (x + tol < y) ? -1 : 0 : 1;
}

template<class T> bool uin(T &a,T b) {return a > b ? (a=b, true):false;}
template<class T> bool uax(T &a,T b) {return a < b ? (a=b, true):false;}

/////////////////////////////////////////////////////////////////////

const int nax = 2e5+10;
ll t[4*nax];
ll l1[4*nax]; // increase each value by x
ll l2[4*nax];
ll a[nax];
int n, q;

void build(int v=1, int tl=0, int tr=n-1){
    if (tl == tr)
        t[v] = a[tl];
    else {
        int tm = (tl + tr) / 2;
        build(v * 2, tl, tm);
        build(v * 2 + 1, tm + 1, tr);
        t[v] = t[v * 2] + t[v * 2 + 1];
    }
}

void push(int v, int tl, int tr){
    if(l2[v]){
        t[v] = (tr-tl+1)*l2[v];
        if(tl!=tr){
            l2[2*v] = l2[v];
            l1[2*v] = 0;
            l2[2*v+1] = l2[v];
            l1[2*v+1] = 0;
        }
        l2[v] = 0;
    }
    if(l1[v]){
        t[v] += (tr-tl+1)*l1[v];
        if(tl!=tr){
            l1[2*v] += l1[v];
            l1[2*v+1] += l1[v];
        }
        l1[v] = 0;
    }
}

void update(int v, int tl, int tr, int l, int r, int value, int type){
    push(v, tl, tr);
    if(l>r) return;
    if(l==tl && tr==r){
        if(type==1){
            l1[v] += value;
        }else{
            l2[v] = value;
            l1[v] = 0;
        }
        push(v, tl, tr);
    }else{
        int tm = (tl+tr)/2;
        update(2*v, tl, tm, l, min(r, tm), value, type);
        update(2*v+1, tm+1, tr, max(l, tm+1), r, value, type);
        t[v] = t[2*v] + t[2*v+1];
    }
}

ll sum(int v, int tl, int tr, int l, int r) {
    if (l > r)
        return 0;
    push(v, tl, tr);
    if (l == tl && r == tr) {
        return t[v];
    }
    int tm = (tl + tr) / 2;
    return sum(v * 2, tl, tm, l, min(r, tm)) +
        sum(v * 2 + 1, tm + 1, tr, max(l, tm + 1), r);
}

int main() {
    sd2(n,q);
    REP(i,n) sl(a[i]);
    build();
    REP(i,q){
        dsd(type);
        if(type==1){
            dsd3(A,B,X);
            update(1, 0, n-1, A-1, B-1, X, 1);
        }else if(type==2){
            dsd3(A,B,X);
            update(1, 0, n-1, A-1, B-1, X, 2);
        }else{
            dsd2(A,B);
            pl(sum(1, 0, n-1, A-1, B-1));
        }
    }
    return 0;
}

// Do something instead of nothing, stay organised, stay ahead!, WRITE STUFF DOWN
