/* قراءة ملفات PDF داخل المتصفح: طبقة نص إن وجدت، وإلا قراءة ضوئية محلية. لا يخرج أي شيء من الجهاز. */
(function(root){
'use strict';
const AR='٠١٢٣٤٥٦٧٨٩',FA='۰۱۲۳۴۵۶۷۸۹';
function normDigits(s){return String(s||'').replace(/[٠-٩]/g,c=>AR.indexOf(c)).replace(/[۰-۹]/g,c=>FA.indexOf(c)).replace(/[٫]/g,'.').replace(/[٬،]/g,',')}
/* ---------- ميزات الحرف ---------- */
const N=12;
function featOf(mask,w,h,yb,yt,H){
  const f=new Float32Array(N*N+5);
  for(let j=0;j<N;j++){const y0=j*h/N,y1=(j+1)*h/N;for(let i=0;i<N;i++){const x0=i*w/N,x1=(i+1)*w/N;let s=0,a=0;
    for(let y=Math.floor(y0);y<Math.ceil(y1);y++){const wy=Math.min(y+1,y1)-Math.max(y,y0);if(wy<=0)continue;for(let x=Math.floor(x0);x<Math.ceil(x1);x++){const wx=Math.min(x+1,x1)-Math.max(x,x0);if(wx<=0)continue;const wt=wx*wy;s+=wt*mask[y*w+x];a+=wt}}
    f[j*N+i]=a?s/a:0}}
  f[N*N]=h/H*2;f[N*N+1]=w/H*2;f[N*N+2]=Math.min(w/Math.max(h,1),2);f[N*N+3]=yb/H*2;f[N*N+4]=yt/H*2;return f}
function dist(a,b){let s=0;const n=N*N;for(let i=0;i<n;i++){const d=a[i]-b[i];s+=d*d}for(let i=n;i<n+5;i++){const d=a[i]-b[i];s+=4*d*d}return s}
let TR=null;
async function loadTrain(url){if(TR)return TR;const j=await (await fetch(url||'digits.json')).json();TR={l:j.l,f:j.f.map(a=>Float32Array.from(a)),dmax:j.dmax,smax:j.smax};return TR}
function setTrain(j){TR={l:j.l,f:j.f.map(a=>Float32Array.from(a)),dmax:j.dmax,smax:j.smax}}
function classify(f,allow){let b1=1e9,c1='',b2=1e9;const best={};
  for(let i=0;i<TR.f.length;i++){const c=TR.l[i];if(allow.indexOf(c)<0)continue;const d=dist(f,TR.f[i]);if(best[c]===undefined||d<best[c])best[c]=d}
  for(const c in best){if(best[c]<b1){b2=b1;b1=best[c];c1=c}else if(best[c]<b2)b2=best[c]}
  return{c:c1,d:b1,m:b2-b1}}
/* ---------- معالجة الصورة ---------- */
function otsu(g){const h=new Uint32Array(256);for(let i=0;i<g.length;i++)h[g[i]]++;let tot=g.length,sum=0;for(let i=0;i<256;i++)sum+=i*h[i];let sb=0,wb=0,mx=0,t=128;for(let i=0;i<256;i++){wb+=h[i];if(!wb)continue;const wf=tot-wb;if(!wf)break;sb+=i*h[i];const mb=sb/wb,mf=(sum-sb)/wf,v=wb*wf*(mb-mf)*(mb-mf);if(v>mx){mx=v;t=i}}return t}
function bandsOf(bin,W,Hh){const out=[];let s=-1;for(let y=0;y<Hh;y++){let on=false;const o=y*W;for(let x=0;x<W;x++){if(bin[o+x]){on=true;break}}
  if(on&&s<0)s=y;else if(!on&&s>=0){out.push([s,y]);s=-1}}if(s>=0)out.push([s,Hh]);
  const m=[];for(const b of out){if(m.length&&b[0]-m[m.length-1][1]<=2)m[m.length-1][1]=b[1];else m.push(b.slice())}return m}
function ccl(bin,W,y0,y1){const h=y1-y0,lab=new Int32Array(W*h),par=[0];let nl=0;
  const find=a=>{while(par[a]!==a){par[a]=par[par[a]];a=par[a]}return a};
  for(let y=0;y<h;y++){for(let x=0;x<W;x++){if(!bin[(y+y0)*W+x])continue;const nb=[];
    if(x>0&&lab[y*W+x-1])nb.push(lab[y*W+x-1]);if(y>0){for(let dx=-1;dx<=1;dx++){const xx=x+dx;if(xx>=0&&xx<W&&lab[(y-1)*W+xx])nb.push(lab[(y-1)*W+xx])}}
    if(!nb.length){nl++;par[nl]=nl;lab[y*W+x]=nl}else{let m=nb[0];for(const v of nb)if(v<m)m=v;lab[y*W+x]=m;for(const v of nb){const a=find(v),b=find(m);if(a!==b){if(a<b)par[b]=a;else par[a]=b}}}}}
  const map=new Int32Array(nl+1),boxes={};let k=0;
  for(let i=1;i<=nl;i++){const r=find(i);if(!map[r])map[r]=++k}
  const bb=[];for(let i=0;i<k;i++)bb.push([1e9,1e9,-1,-1,0]);
  for(let y=0;y<h;y++)for(let x=0;x<W;x++){const v=lab[y*W+x];if(!v)continue;const id=map[find(v)];lab[y*W+x]=id;const b=bb[id-1];if(x<b[0])b[0]=x;if(y<b[1])b[1]=y;if(x>b[2])b[2]=x;if(y>b[3])b[3]=y;b[4]++}
  return{lab,boxes:bb.map((b,i)=>({id:i+1,x0:b[0],y0:b[1]+y0,x1:b[2]+1,y1:b[3]+1+y0,n:b[4]}))}}
function maskOf(lab,W,y0,c){const w=c.x1-c.x0,h=c.y1-c.y0,m=new Uint8Array(w*h),ids=c.ids||[c.id];for(let y=0;y<h;y++)for(let x=0;x<w;x++){const v=lab[(c.y0-y0+y)*W+c.x0+x];if(v&&(ids.length===1?v===ids[0]:ids.indexOf(v)>=0))m[y*w+x]=1}return m}
function estimateH(all){const hist={};for(const c of all){const w=c.x1-c.x0,h=c.y1-c.y0;if(h<12||h>60||w/h<0.35||w/h>1.4)continue;hist[h]=(hist[h]||0)+1}
  const sm=h=>(hist[h-1]||0)+(hist[h]||0)+(hist[h+1]||0);let mx=0;for(let h=17;h<=50;h++)mx=Math.max(mx,sm(h));
  for(let h=17;h<=50;h++){const v=sm(h);if(v>=0.25*mx&&v>=sm(h-1)&&v>=sm(h+1))return h}return 21}
/* ---------- تحليل صفحة ممسوحة ---------- */
async function pageToRows(gray,W,Hh,worker,opt){
  opt=opt||{};const t=Math.min(Math.max(otsu(gray),90),200);const bin=new Uint8Array(W*Hh);for(let i=0;i<bin.length;i++)bin[i]=gray[i]<t?1:0;
  let bands=bandsOf(bin,W,Hh).filter(b=>b[1]-b[0]>=8);
  const data=[];const all=[];
  for(const b of bands){const r=ccl(bin,W,b[0],b[1]);r.boxes=r.boxes.filter(c=>c.n>=3&&(c.x1-c.x0)<W*0.5);data.push({b,r});r.boxes.forEach(c=>all.push(c))}
  const left=all.filter(c=>(c.x0+c.x1)/2<W*0.55);const H=opt.H||estimateH(left.length>40?left:all);
  const rows=[];
  for(const d of data){const {b,r}=d;let cs=r.boxes.slice().sort((p,q)=>p.x0-q.x0);if(!cs.length)continue;
    {const mg=[];for(const c of cs){const pr=mg.length?mg[mg.length-1]:null;
      if(pr){const ov=Math.min(pr.x1,c.x1)-Math.max(pr.x0,c.x0),mw=Math.min(pr.x1-pr.x0,c.x1-c.x0);const nh=Math.max(pr.y1,c.y1)-Math.min(pr.y0,c.y0);
        if(ov>0.5*mw&&nh<=1.3*H&&mw>=4&&(pr.x1-pr.x0)<1.3*H&&(c.x1-c.x0)<1.3*H){pr.ids=(pr.ids||[pr.id]).concat(c.ids||[c.id]);pr.x0=Math.min(pr.x0,c.x0);pr.x1=Math.max(pr.x1,c.x1);pr.y0=Math.min(pr.y0,c.y0);pr.y1=Math.max(pr.y1,c.y1);pr.n+=c.n;continue}}
      mg.push(Object.assign({},c))}cs=mg}
    const chunks=[];let cur=[];for(const c of cs){if(cur.length&&c.x0-Math.max(...cur.map(k=>k.x1))>1.0*H){chunks.push(cur);cur=[]}cur.push(c)}if(cur.length)chunks.push(cur);
    const toks=[],used=new Set();
    for(const ch of chunks){const ty=[];const typ=ch.map(c=>{const w=c.x1-c.x0,h=c.y1-c.y0;
        if(h>=0.65*H&&h<=1.3*H&&w<=1.3*H)return'd';if(h>1.28*H&&h<=2.1*H&&w<=0.55*H)return'p';if(h<0.62*H&&w<=0.62*H&&c.n>=3)return's';if(h<=0.22*H&&w>=0.3*H&&w<=1.1*H)return'-';return'x'});
      if(typ.includes('x')){if(opt.debug)(d.dbg=d.dbg||[]).push({x:ch[0].x0,why:'x',typ:typ.join(''),sz:ch.map(c=>(c.x1-c.x0)+'x'+(c.y1-c.y0)).join(' ')});continue}const tall=ch.filter((c,i)=>typ[i]==='d'&&(c.y1-c.y0)>=0.8*H);
      let B=null;if(tall.length){const bs=tall.map(c=>c.y1).sort((p,q)=>p-q);B=bs[bs.length>>1]}
      if(B!==null)ch.forEach((c,i)=>{if(typ[i]==='d'&&(c.y1-c.y0)<0.78*H&&(c.x1-c.x0)<=0.5*H&&c.y1>=B+0.12*H)typ[i]='s'});
      let unk=0,txt='',ok=true,dsum=0,dn=0,neg=false,minM=1e9;
      if(!tall.length){ // رمز واحد: نقطة أو شرطة تعني صفر
        if(ch.length===1&&(typ[0]==='s'||typ[0]==='-')){toks.push({x0:ch[0].x0,x1:ch[0].x1,v:0,raw:'\u0660',weak:true,d:0,m:99,comps:ch});}
        continue}
      for(let i=0;i<ch.length&&ok;i++){const c=ch[i],ty0=typ[i];
        if(ty0==='p'){neg=true;continue}
        if(ty0==='-'){continue}
        const w=c.x1-c.x0,h=c.y1-c.y0,m=maskOf(r.lab,W,b[0],c);
        const f=featOf(m,w,h,c.y1-B,c.y0-B,H);
        if(ty0==='s'){txt+=(c.y1>=B+0.1*H)?',':'0';dn++;continue}
        const cl=classify(f,'123456789');
        if(cl.d>TR.dmax){unk++;txt+='?';continue}
        txt+=cl.c;dsum+=cl.d;dn++;minM=Math.min(minM,cl.m)}
      if(!ok||!/[0-9]/.test(txt.replace(/\?/g,''))){if(opt.debug)(d.dbg=d.dbg||[]).push({x:ch[0].x0,why:'cls',txt,typ:typ.join('')});continue}
      if(unk>0&&(unk>2||unk*2>dn+unk)){if(opt.debug)(d.dbg=d.dbg||[]).push({x:ch[0].x0,why:'unk',txt});continue}
      const dg=txt.replace(/,/g,'');
      /* تحقق من شكل الفواصل */
      if(txt.includes(',')){const p=txt.split(',');if(!(p[0].length>=1&&p[0].length<=3&&p.slice(1).every(x=>x.length===3))){if(opt.debug)(d.dbg=d.dbg||[]).push({x:ch[0].x0,why:'fmt',txt});continue}}
      toks.push({x0:ch[0].x0,x1:ch[ch.length-1].x1,v:unk?null:(neg?-1:1)*parseInt(dg,10),raw:txt,unk:unk,weak:(dg.length<=2&&!txt.includes(',')),d:dsum/Math.max(dn,1),m:minM,comps:ch})}
    // قبول الرموز الضعيفة فقط إذا وُجد ما يحاذيها
    const strong=toks.filter(k=>!k.weak),ctr=k=>(k.x0+k.x1)/2;
    const accepted=toks.filter(k=>!k.weak||toks.filter(o=>o!==k&&Math.abs(ctr(o)-ctr(k))<2*H).length>=0||true);
    d.toks=accepted}
  // دعم الرموز الضعيفة بمحاذاة رموز من أسطر أخرى
  const allT=[];data.forEach((d,i)=>(d.toks||[]).forEach(k=>allT.push(k)));
  for(const d of data){d.toks=(d.toks||[]).filter(k=>{if(!k.weak)return true;const c=(k.x0+k.x1)/2;return allT.filter(o=>o!==k&&Math.abs((o.x0+o.x1)/2-c)<1.6*H).length>=2})}
  // تسمية
  const clean=document.createElement('canvas');clean.width=W;clean.height=Hh;
  for(const d of data){const {b,r}=d;const tk=new Set();d.toks.forEach(k=>k.comps.forEach(c=>(c.ids||[c.id]).forEach(i=>tk.add(i))));
    const lc=r.boxes.filter(c=>!tk.has(c.id)&&(c.y1-c.y0)<2.6*H);let label='';
    if(lc.length>=2&&opt.labels!==false){const x0=Math.max(0,Math.min(...lc.map(c=>c.x0))-8),x1=Math.min(W,Math.max(...lc.map(c=>c.x1))+8),y0=Math.max(0,b[0]-6),y1=Math.min(Hh,b[1]+6);
      const cw=x1-x0,chh=y1-y0;if(cw>10&&chh>5){const cv=document.createElement('canvas');cv.width=cw;cv.height=chh;const cx=cv.getContext('2d'),im=cx.createImageData(cw,chh);
        const keep=new Set(lc.map(c=>c.id));
        for(let y=0;y<chh;y++)for(let x=0;x<cw;x++){const yy=y+y0,xx=x+x0;let v=255;if(yy>=b[0]&&yy<b[1]){const id=r.lab[(yy-b[0])*W+xx];if(id&&keep.has(id))v=0}const o=(y*cw+x)*4;im.data[o]=im.data[o+1]=im.data[o+2]=v;im.data[o+3]=255}
        cx.putImageData(im,0,0);
        try{const res=await worker.recognize(cv);label=(res.data.text||'').replace(/\s+/g,' ').trim()}catch(e){label=''}}}
    const vals=d.toks.map(k=>({x:(k.x0+k.x1)/2,v:k.v,raw:k.raw,d:k.d,unk:k.unk})).sort((p,q)=>q.x-p.x);
    if(label||vals.length)rows.push({y:b[0],label,vals,H,dbg:d.dbg})}
  return{rows,H,thr:t}}
function estPageH(gray,W,Hh){const t=Math.min(Math.max(otsu(gray),90),200);const bin=new Uint8Array(W*Hh);for(let i=0;i<bin.length;i++)bin[i]=gray[i]<t?1:0;
  const all=[];for(const b of bandsOf(bin,W,Hh).filter(b=>b[1]-b[0]>=8)){const r=ccl(bin,W,b[0],b[1]);r.boxes.filter(c=>c.n>=3&&(c.x1-c.x0)<W*0.5).forEach(c=>all.push(c))}
  const left=all.filter(c=>(c.x0+c.x1)/2<W*0.55);return left.length>40?estimateH(left):0}
/* ---------- صفحة بطبقة نص ---------- */
function textPageRows(items){const its=items.filter(i=>i.str&&i.str.trim()).map(i=>({s:i.str.trim(),x:i.transform[4],y:i.transform[5],w:i.width||0}));
  its.sort((a,b)=>b.y-a.y||a.x-b.x);const rows=[];let cur=null;
  for(const it of its){if(!cur||Math.abs(cur.y-it.y)>3){cur={y:it.y,items:[]};rows.push(cur)}cur.items.push(it)}
  return rows.map(r=>{const labs=[],vals=[];r.items.sort((a,b)=>b.x-a.x);
    for(const it of r.items){const n=normDigits(it.s).replace(/\s/g,'');if(/^[\(\-]?\d[\d,]*(\.\d+)?\)?$/.test(n)){let v=parseFloat(n.replace(/[(),]/g,''));if(/^\(.*\)$/.test(n)||/^-/.test(n))v=-Math.abs(v);vals.push({x:it.x+it.w/2,v,raw:n,d:0})}else labs.push(it.s)}
    return{y:-r.y,label:labs.join(' ').replace(/\s+/g,' ').trim(),vals,H:12}}).filter(r=>r.label||r.vals.length)}
/* ---------- الواجهة العامة ---------- */
async function readPdf(file,cb,opt){
  opt=opt||{};const base=opt.base||'';cb=cb||function(){};
  const pdfjs=root.pdfjsLib;if(!pdfjs)throw new Error('pdfjs missing');
  pdfjs.GlobalWorkerOptions.workerSrc=base+'pdf.worker.min.js';
  const doc=await pdfjs.getDocument({data:new Uint8Array(await file.arrayBuffer())}).promise;
  const pages=[];let worker=null;
  async function renderGray(pg){const v0=pg.getViewport({scale:1});let sc=300/72;const mx=Math.max(v0.width,v0.height)*sc;if(mx>4200)sc*=4200/mx;
    const vp=pg.getViewport({scale:sc});const cv=document.createElement('canvas');cv.width=Math.round(vp.width);cv.height=Math.round(vp.height);
    const cx=cv.getContext('2d',{willReadFrequently:true});cx.fillStyle='#fff';cx.fillRect(0,0,cv.width,cv.height);
    await pg.render({canvasContext:cx,viewport:vp}).promise;
    const im=cx.getImageData(0,0,cv.width,cv.height).data;const g=new Uint8Array(cv.width*cv.height);for(let i=0,j=0;j<g.length;i+=4,j++)g[j]=(im[i]*0.3+im[i+1]*0.59+im[i+2]*0.11)|0;
    const W=cv.width,Hh=cv.height;cv.width=cv.height=1;return{g,W,Hh}}
  let Hdoc=0;{const ests=[];for(let p=1;p<=doc.numPages&&ests.length<4;p++){const pg=await doc.getPage(p);const tc=await pg.getTextContent();if(tc.items.reduce((s,i)=>s+(i.str||'').trim().length,0)>=40)continue;
      cb({stage:'prep',page:p,total:doc.numPages});await new Promise(r=>setTimeout(r,0));const r=await renderGray(pg);const e=estPageH(r.g,r.W,r.Hh);if(e)ests.push(e)}
    ests.sort((a,b)=>a-b);if(ests.length)Hdoc=ests[(ests.length-1)>>1]}
  try{
    for(let p=1;p<=doc.numPages;p++){if(opt.only&&opt.only.indexOf(p)<0)continue;
      cb({stage:'page',page:p,total:doc.numPages});await new Promise(r=>setTimeout(r,0));
      const pg=await doc.getPage(p);const tc=await pg.getTextContent();const chars=tc.items.reduce((s,i)=>s+(i.str||'').trim().length,0);
      if(chars>=40){pages.push({n:p,mode:'text',rows:textPageRows(tc.items)});continue}
      if(!worker){cb({stage:'load',page:p,total:doc.numPages});await loadTrain(base+'digits.json');
        worker=await root.Tesseract.createWorker('ara',1,{workerPath:base+'worker.min.js',corePath:base,langPath:base,cacheMethod:'none',gzip:true,logger:()=>{}});
        await worker.setParameters({tessedit_pageseg_mode:'7',preserve_interword_spaces:'1'})}
      const rg=await renderGray(pg);const g=rg.g;
      cb({stage:'ocr',page:p,total:doc.numPages});await new Promise(r=>setTimeout(r,0));
      const r=await pageToRows(g,rg.W,rg.Hh,worker,Object.assign({},opt,{H:Hdoc||0}));
      pages.push({n:p,mode:'ocr',rows:r.rows,H:r.H})}
  }finally{if(worker)await worker.terminate()}
  return{pages,numPages:doc.numPages}}
root.PDFIMP={readPdf,featOf,classify,setTrain,normDigits,N,pageToRows,loadTrain,_otsu:otsu,_bandsOf:bandsOf,_ccl:ccl,_maskOf:maskOf,_estimateH:estimateH};
if(typeof module!=='undefined')module.exports=root.PDFIMP;
})(typeof window!=='undefined'?window:globalThis);
