// Push-optimal Sokoban: each room of the level is solved by breadth-first search over pushes (dead squares and
// frozen blocks pruned), so the first solved state is the room's optimum; a level's rooms are independent and their
// optima add up. No clock, no randomness: the same bytes on every run.
import{readdirSync as D,readFileSync as F,writeFileSync as W,mkdirSync as M}from'node:fs';
import{join as J}from'node:path';
const I=process.env.MAKEFUN_INPUT_DIR||'/input',O=process.env.MAKEFUN_OUTPUT_DIR||'/output',X=[0,0,-1,1],Y=[-1,1,0,0],C='udlr';
const P=t=>{const r=t.split('\n').filter(a=>a),h=r.length,w=Math.max(...r.map(a=>a.length)),wl=new Uint8Array(w*h).fill(1),gs=[],bs=[];let pl=0;
for(let y=0;y<h;y++)for(let x=0;x<r[y].length;x++){const c=r[y][x],i=y*w+x;if(c!='#'){wl[i]=0;if('.*+'.includes(c))gs.push(i);if('$*'.includes(c))bs.push(i);if('@+'.includes(c))pl=i}}
return{w,wl,gs,bs:bs.sort((a,b)=>a-b),pl}};
const V=L=>{const{w,wl,gs}=L,l=new Uint8Array(wl.length),q=[...gs];gs.map(g=>l[g]=1);
for(let i=0;i<q.length;i++)for(let k=4;k--;){const d=Y[k]*w+X[k],y=q[i]-d;if(!wl[y]&&!wl[y-d]&&!l[y])l[y]=1,q.push(y)}
return l};
const R=(L,o,f,s,t)=>{const{w,wl}=L,q=[f];let lo=f;s[f]=t;
for(let i=0;i<q.length;i++){const p=q[i];if(p<lo)lo=p;for(let j=4;j--;){const n=p+Y[j]*w+X[j];if(!wl[n]&&!o[n]&&s[n]!=t)s[n]=t,q.push(n)}}
return lo};
const Z=(L,o,g,t)=>{const{w,wl}=L;for(const a of[t,t-1,t-w,t-w-1]){const b=a+1,c=a+w,d=c+1;
if((wl[a]|o[a])&(wl[b]|o[b])&(wl[c]|o[c])&(wl[d]|o[d])&((o[a]&!g[a])|(o[b]&!g[b])|(o[c]&!g[c])|(o[d]&!g[d])))return 1}};
const K=(L,o,f,t)=>{const{w,wl}=L,pv=new Int32Array(wl.length).fill(-1),hw=[],q=[f];pv[f]=f;
for(let i=0;i<q.length&&pv[t]<0;i++){const p=q[i];for(let j=4;j--;){const n=p+Y[j]*w+X[j];if(!wl[n]&&!o[n]&&pv[n]<0)pv[n]=p,hw[n]=j,q.push(n)}}
if(pv[t]<0)return'';
let s='';for(let p=t;p!=f;p=pv[p])s=C[hw[p]]+s;return s};
const B=L=>{const{w,wl,gs,bs,pl}=L,N=wl.length,g=new Uint8Array(N);gs.map(x=>g[x]=1);
const l=V(L),o=new Uint8Array(N),s=new Int32Array(N),m=new Int32Array(N);let st=0;
const ky=(b,lo)=>{let k=lo;for(const x of b)k=k*N+x;return k},ok=b=>b.every(x=>g[x]);
const S=[bs],Q=[pl],PR=[-1],ix=new Map();
bs.map(x=>o[x]=1);ix.set(ky(bs,R(L,o,pl,s,++st)),0);bs.map(x=>o[x]=0);
let fn=ok(bs)?0:-1;
for(let h=0;fn<0&&h<S.length;h++){const bx=S[h];bx.map(x=>o[x]=1);
R(L,o,Q[h],s,++st);const hr=st;
for(let i=0;i<bx.length&&fn<0;i++){const b=bx[i];
for(let k=0;k<4;k++){const d=Y[k]*w+X[k],t=b+d;
if(s[b-d]!=hr||wl[t]||o[t]||!l[t])continue;
o[b]=0;o[t]=1;const z=Z(L,o,g,t);let nx,kk;
if(!z){nx=bx.slice();nx[i]=t;nx.sort((a,b)=>a-b);kk=ky(nx,R(L,o,b,m,++st))}
o[t]=0;o[b]=1;
if(z||ix.has(kk))continue;
ix.set(kk,S.length);S.push(nx);Q.push(b);PR.push(h);
if(ok(nx))fn=S.length-1}}
bx.map(x=>o[x]=0)}
if(fn<0)return null;
const p=[];for(let i=fn;i>0;i=PR[i])p.push(i);p.reverse();
let mv='',q0=L.pl,b0=bs;
for(const i of p){const nx=S[i],a=b0.find(b=>!nx.includes(b)),z=nx.find(b=>!b0.includes(b)),d=z-a;
b0.map(b=>o[b]=1);mv+=K(L,o,q0,a-d);b0.map(b=>o[b]=0);
mv+=d==-w?'u':d==w?'d':d==-1?'l':'r';q0=a;b0=nx}
return{p:p.length,mv,pl:q0}};
const A=L=>{const{w,wl,gs,bs,pl}=L,ct=wl.slice(),N=wl.length;
for(let i=Math.floor(pl/w)*w;i<Math.floor(pl/w)*w+w;i++)ct[i]=1;
const pt=new Int32Array(N).fill(-1),R=[];
for(let i=0;i<N;i++){if(ct[i]||pt[i]>=0)continue;const q=[i];pt[i]=R.length;
for(let j=0;j<q.length;j++)for(let k=4;k--;){const n=q[j]+Y[k]*w+X[k];if(!ct[n]&&pt[n]<0)pt[n]=R.length,q.push(n)}
R.push({b:[],g:[]})}
for(const b of bs)R[pt[b]].b.push(b);
for(const g of gs)R[pt[g]].g.push(g);
return R.some(r=>r.b.length!=r.g.length)?null:R.filter(r=>r.b.length)};
const S0=L=>{const R=A(L);if(!R)return null;let pl=L.pl,mv='';
for(const r of R){const wl=L.wl.slice();
for(const o of R)if(o!=r)for(const b of o.d?o.g:o.b)wl[b]=1;
const one=B({w:L.w,wl,gs:r.g,bs:r.b,pl});if(!one)return null;
mv+=one.mv;pl=one.pl;r.d=1}
return mv};
for(const id of D(I).sort()){const m=S0(P(F(J(I,id,'level.txt'),'utf8')));M(J(O,id),{recursive:true});W(J(O,id,'solution.txt'),(m||'')+'\n')}
