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

const int nax = 1e5+10;

ll t[4*nax];
ll a[nax];
ll lazy[4*nax];
int n,c;

void push(int v, int l, int r){
    t[v] += (r - l + 1)*lazy[v];
    if(l!=r){ // if the node has children we propagate the lazy
    	lazy[v*2] += lazy[v];
    	lazy[v*2+1] += lazy[v];
    }
    lazy[v]=0;
}

void update(int v, int tl, int tr, int l, int r, int value){
    push(v, tl, tr);
    if (l > r) 
        return;
    if(l == tl && tr == r){
        lazy[v] += value;
        push(v,l,r);
    }
    else{
        int tm=(tl+tr)/2;
        update(2*v, tl, tm, l, min(r, tm), value);
        update(2*v+1, tm+1, tr, max(l, tm+1), r, value);
        t[v] = t[2*v] + t[2*v+1]; // children are up to date because we always push
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
    dsd(TC);
    while(TC--){
        sd2(n,c);
        REP(i,4*n) t[i]=0;
        REP(i,4*n) lazy[i]=0;
        while(c--){
            dsd(type);
            if(type==0){
                dsd3(p,q,v);
                update(1,0,n-1,p-1,q-1,v);
            }else{
                dsd2(p,q);
                pl(sum(1,0,n-1,p-1,q-1));
            }
            debug() << imie(range(t, t+16));
        }
    }
    return 0;
}

// Do something instead of nothing, stay organised, stay ahead!, WRITE STUFF DOWN
