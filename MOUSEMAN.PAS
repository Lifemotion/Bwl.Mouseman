{$I-}
program filemanager;
uses graph,crt,dos;
type windowtype=record
     x,y,h,w:integer;
     caption:string;
     active:integer;
     icon:integer;
     wc1,wc2,bc1,bc2:pointer;
     ws1,ws2,bs1,bs2:word;
end;
buttonstype=record
     x,y,h,w,bw,pic:integer;
     ft,fs,dw:integer;
     text:string;
     rel:byte;
end;
bmphead=record
     ftype:word;
     size:longint;
     rezerved:longint;
     offset:longint;
end;
bmpinfo=record
     size:longint;
     width:longint;
     height:longint;
     planes:word;
     bits:word;
     compr:longint;
     fsize:longint;
     xpm:longint;
     ypm:longint;
     clrused:longint;
     clrimp:longint;
end;
rgbquad=record
     red:byte;
     green:byte;
     blue:byte;
     reserverd:byte;
end;
artype=array[0..0] of byte;
arptr=^artype;
bmpfile16=record
     image:arptr;
     fcl:integer;
     w,wr:integer;
     h:integer;
     apal:array[0..15] of byte;
end;
type
pft=^filestype;
filestype=record
    index:integer;
    name:string[12];
    capt:string;
    ext:string[3];
    size:longint;
    date:string[10];
    time:string[6];
    adir:boolean;
    aro:boolean;
    ahd:boolean;
    next:pft;
    prev:pft;
end;
type
    tlfn = record
    attr : longint;
    creation : comp;
    lastaccess : comp;
    lastmodification : comp;
    highfilesize : longint;
    lowfilesize : longint;
    reserved : comp;
    name : array[0..259] of char;
    shortname : array[0..13] of char;
    handle : word;
end;
{общие}

var exitfl,alldrive:byte;startdir:string;
var pal,cpal:array[0..15,0..2] of byte;
var wnd:array[1..10] of windowtype;
var btn:array[1..60] of buttonstype;
var wndpos:array[1..10] of integer; allwnd,lastwnd:integer;
var key1,key2:char;
var mbmp:array[1..30] of bmpfile16;
var needinit:integer;
var awx,awy:integer;
var menu:array[1..10] of string;allmenu:integer;
var notasking:byte;lastmin:word;
{файлового менеджера}
var fmtab:byte;
var fmpath:array[1..2] of string;
var fmpos:array[1..2] of pft;
var fmsel:array[1..2] of pft;
var files:array[1..2] of pft;
var allfile:array[1..2] of integer;
var cfile:pft;
var plainrefr:byte;
const fmpagesize=30;fmtaby=60;
const fmstroke=10;
const lfn=1;
{просмотрщика}
var vwfile:string;
var vwmode:byte;
var vwext:string[3];
var vwsz,vwdx,vwdy:integer;
var vwpis:integer;
{сообщения}
var mstext:string;
var msanswer:string;
var msready:byte;
var msinp:byte;
var msevnt:byte;
var needevent:byte;
{виселицы}
var vword,vtry:string;
var vmist,vlen,vvern,vwin:integer;

procedure Show;assembler;
  asm
   mov ax,1
   int $33
    end;
procedure Hide;assembler;
  asm
   mov ax,2
   int $33
  end;
procedure InitMouse;assembler;
  asm
   mov ax,0
   int $33
   mov ax,1
   int $33
  end;
procedure GetMouse(var x,y,b:word);
var Reg:Registers;
 begin
  with Reg do
   begin
    ax:=3;
    Intr($33,Reg);
    b:=bx;
    x:=cx;
    y:=dx;
   end;
 end;
function findfirst_l(filespec:string;attr:word;var S:tlfn):integer;
begin
     filespec := filespec + #0;
     S.attr := attr;
     asm
     push ds
     push ss
     pop ds
     lea dx,filespec+1
     les di,S
     mov ax,$714e
     mov cx,attr
     mov si,0
     int $21
     les di,S
     mov word ptr es:[di+tlfn], ax
     jc @1
     xor ax,ax
     @1:
     mov @result,ax
     pop ds
end;
end;

function FindClose(var S:tlfn):integer;
begin
     asm
     mov ax,$71a1
     les di,S
     mov bx,word ptr es:[di+tlfn.Handle]
     int $21
     jc @1
     xor ax,ax
     @1:
     mov @result,ax
end;
end;

function getlfn(path:string):string;
var S:tlfn; Res:Integer;
var n:integer;st:string;
begin
     Res := findfirst_l(path,AnyFile-VolumeID,S);
     n:=0;st:='';
     if res=0 then begin
        while s.name[n]<>#0 do begin
        st:=st+s.name[n];
        n:=n+1;
        end;
        getlfn:=st;
     end;
     if res<>0 then getlfn:='';
     FindClose(S);
end;

function stri(int:integer):string;
var st:string;
begin
     str(int,st);
     stri:=st;
end;


function clrconv16(r,g,b:byte):byte;
var const1,const2,const3:byte;
var ra,ba,ga,ya,cs,y:byte;
begin
const1 := 80;
const2 := 130;
const3 := 210;
ya:=0;
IF r > const1 THEN ra:= 1 else ra:=0;
IF g > const1 THEN ga:= 1 else ga:=0;
IF B > const1 THEN ba:= 1 else ba:=0;
IF (r>const2) OR (B>const2) OR (g>const2) THEN ya:= 1;
cs:= ra+ga*2+ba*4+ya*8;

IF ((ga + ra + ba) = 3) OR ((ga + ra + ba) = 0) THEN begin
y:= (r + g + b) div 3;
IF y > const3 THEN cs:= 15;
IF (y <= const3) AND (y>const2) THEN cs:= 7;
IF (y <= const2) AND (y>const1) THEN cs:= 8;
IF y <= const1 THEN cs:= 0;
end;

CLRCONV16:= cs;
end;

procedure loadbmp(filenm:string;fn,freeclr:integer);
var bmph:bmphead;bmpi:bmpinfo;
var pal:array[0..15] of rgbquad;fl:file;
var apal:array[0..15] of byte;
var n,xb,x,y:integer;
var mem:word;cbyte:byte;
begin
     assign(fl,filenm);
     reset(fl,1);
     blockread(fl,bmph,sizeof(bmph));
     blockread(fl,bmpi,sizeof(bmpi));
     seek(fl,54);

     for n:=0 to 15 do begin
         blockread(fl, pal[n],4);
         mbmp[fn].apal[n]:=clrconv16(pal[n].red,pal[n].green,pal[n].blue);
     end;

     seek(fl,bmph.offset);
     if bmpi.bits=4 then xb:=(bmpi.width div 2)+(bmpi.width mod 2);
     if bmpi.bits<>4 then runerror(1);
     if (xb mod 4)>0 then xb:=4+xb-(xb mod 4);
     with mbmp[fn] do begin
          w:=bmpi.width;
          h:=bmpi.height;
          wr:=xb;
          fcl:=freeclr;
          getmem(image,(xb*h));

          for y:=0 to h-1 do
              for x:=0 to xb-1 do begin
                  blockread(fl,cbyte,1,mem);
                  image^[(y*xb)+x]:=cbyte;
              end;
     end;
     close(fl);
end;

procedure drawbmp(fn,xp,yp:integer);
var x,y,wt:integer;
var tmp,cl1,cl2:byte;

begin
with mbmp[fn] do begin
     wt:=w div 2;
     for y:=0 to h-1 do
          for x:=0 to wt-1 do begin
             tmp:=image^[(y*wr)+x];
             {if x<=wt then begin}
             cl1:=apal[tmp div 16];cl2:=apal[tmp mod 16];
             if cl1<>fcl then putpixel(xp+x*2,yp+(h-y),cl1);
             if cl2<>fcl then putpixel(xp+x*2+1,yp+(h-y),cl2);
          end;
     end;
end;

procedure viewbmp(fn:string;xp,yp,dx,dy,sz:integer);
var bmph:bmphead;bmpi:bmpinfo;
var pal:array[0..255] of rgbquad;fl:file;
var apal:array[0..15] of byte;
var n,xb,x,y,h,w:integer;
var cbyte,cl1,cl2:byte;
var mx,my,maxy:integer;
var xarr:array[0..1024]of byte;
begin
     assign(fl,fn);
     reset(fl,1);
     blockread(fl,bmph,sizeof(bmph));
     blockread(fl,bmpi,sizeof(bmpi));
     seek(fl,54);

     for n:=0 to 15 do begin
         blockread(fl, pal[n],4);
         apal[n]:=clrconv16(pal[n].red,pal[n].green,pal[n].blue);
         {apal[n]:=n;}
     end;

     seek(fl,bmph.offset);
     h:=bmpi.height;
     w:=bmpi.width;
     if bmpi.bits=4 then xb:=(bmpi.width div 2)+(bmpi.width mod 2);
     if bmpi.bits<>4 then runerror(1);
     if (xb mod 4)>0 then xb:=4+xb-(xb mod 4);
     mx:=0;
     my:=0;
          maxy:=(h div sz)-dy;
          if maxy>280 then maxy:=280;
          for y:=0 to bmpi.height-1 do begin
              if bmpi.bits=4 then begin
              for x:=0 to xb-1 do begin
                  blockread(fl,cbyte,1);
                  cl1:=apal[cbyte div 16];
                  cl2:=apal[cbyte mod 16];
                  xarr[x*2]:=cl1;
                  xarr[x*2+1]:=cl2;
              end;
              if (y mod sz)=0 then begin
                  my:=my+1;
                  mx:=0;
                  for x:=0 to w do
                     if (x mod sz=0) then begin
                        mx:=mx+1;
                        if (mx>dx) and (mx<280+dx) and ((h div sz)-my>dy) and ((h div sz)-my<280+dy) then
                           putpixel(xp+mx-dx,yp+(h div sz)-(my+dy),xarr[x]);
                     end;
              end;
              end;

          end;
     close(fl);
end;
procedure viewtxt(fn:string;xp,yp,pos:integer);
var fl:text;
var n,m,d:integer;
var tmp,tmp2:string;
const strsz=10;
begin
     assign(fl,fn);
     reset(fl);
     settextstyle(2,0,4);
     setcolor(0);
     n:=0;m:=0;{pos:=0;}
     while (m<26) and (eof(fl)<>true) do begin
         readln(fl,tmp);
         n:=n+1;
         if n>pos*26 then begin
            hide;
            for d:=0 to (length(tmp) div 45) do begin
                tmp2:=copy(tmp,d*45+1,45);
                if d>0 then begin
                   setcolor (12);
                   outtextxy(xp+10,yp+m*strsz,'');
                   setcolor (0);
                   tmp2:='  '+tmp2;
                end;
                outtextxy(xp+10,yp+m*strsz,tmp2);
                m:=m+1;
            end;
         end;
     end;
     show;
     close(fl);
end;

procedure viewbin(fn:string;xp,yp,pos:integer);
var fl:file;
var n,m,d:integer;
var tmp:array[1..30] of char;
const strsz=10;
begin
     assign(fl,fn);{pos:=0;}
     reset(fl,30);
     settextstyle(0,0,1);
     setcolor(0);
     seek(fl,pos*26);
     m:=0;
      while m<26 do begin
         blockread(fl,tmp,1,d);
         m:=m+1;
         for n:=1 to 30 do
            if d>0 then outtextxy(xp+n*9-5,yp+m*strsz,tmp[n]);
     end;
     show;
     close(fl);
end;

procedure getbmpinfo(fn:string; var x,y:integer);
var bmph:bmphead;bmpi:bmpinfo;
var fl:file;
begin
     assign(fl,fn);
     reset(fl,1);
     blockread(fl,bmph,sizeof(bmph));
     blockread(fl,bmpi,sizeof(bmpi));
     x:=-1;
     if bmph.ftype=19778 then begin
         x:=bmpi.width;
         y:=bmpi.height;
         if bmpi.bits<>4 then x:=-1;
         if (x>1024) or (y>1024) then x:=-1;
     end;
     close(fl);
end;

procedure loadpalette;
begin
     pal[0,0]:=0; pal[0,1]:=0; pal[0,2]:=0;
     pal[1,0]:=0; pal[1,1]:=0; pal[1,2]:=128;
     pal[2,0]:=0; pal[2,1]:=128; pal[2,2]:=0;
     pal[3,0]:=0; pal[3,1]:=64; pal[3,2]:=128;
     pal[4,0]:=128; pal[4,1]:=0; pal[4,2]:=0;
     pal[5,0]:=128; pal[5,1]:=0; pal[5,2]:=128;
     pal[6,0]:=128; pal[6,1]:=128; pal[6,2]:=0;
     pal[7,0]:=192; pal[7,1]:=192; pal[7,2]:=192;
     pal[8,0]:=128; pal[8,1]:=128; pal[8,2]:=128;
     pal[9,0]:=0; pal[9,1]:=0; pal[9,2]:=255;
     pal[10,0]:=0; pal[10,1]:=255; pal[10,2]:=0;
     pal[11,0]:=0; pal[11,1]:=255; pal[11,2]:=255;
     pal[12,0]:=255; pal[12,1]:=0; pal[12,2]:=0;
     pal[13,0]:=255; pal[13,1]:=0; pal[13,2]:=255;
     pal[14,0]:=255; pal[14,1]:=255; pal[14,2]:=0;
     pal[15,0]:=255; pal[15,1]:=255; pal[15,2]:=255;
end;

procedure setpalette(mode:integer);
var n,c,m,z:integer;
begin
     if mode=-1 then begin
        cpal:=pal;
        for z:=0 to 15 do
           if z<>14 then begin
            cpal[z,0]:=0;
            cpal[z,1]:=0;
            cpal[z,2]:=0;
        end;
        for n:=0 to 7 do begin
                setrgbpalette(n,(cpal[n,0] div 4)+192,(cpal[n,1] div 4)+192,(cpal[n,2] div 4)+192);
                setrgbpalette(56+n,(cpal[n+8,0] div 4)+192,(cpal[n+8,1] div 4)+192,(cpal[n+8,2] div 4)+192);
            end;
      end;
     if mode=0 then begin
         for n:=0 to 7 do begin
             setrgbpalette(n,(pal[n,0] div 4)+192,(pal[n,1] div 4)+192,(pal[n,2] div 4)+192);
             setrgbpalette(56+n,(pal[n+8,0] div 4)+192,(pal[n+8,1] div 4)+192,(pal[n+8,2] div 4)+192);
         end;
     end;

     if mode=1 then begin
        for z:=0 to 15 do begin
            cpal[z,0]:=0;
            cpal[z,1]:=0;
            cpal[z,2]:=0;
        end;
        for z:=0 to 255 do begin
            for c:=0 to 15 do begin
                     if cpal[c,0]<pal[c,0] then cpal[c,0]:=cpal[c,0]+1;
                     if cpal[c,1]<pal[c,1] then cpal[c,1]:=cpal[c,1]+1;
                     if cpal[c,2]<pal[c,2] then cpal[c,2]:=cpal[c,2]+1;
            end;
            for n:=0 to 7 do begin
                setrgbpalette(n,(cpal[n,0] div 4)+192,(cpal[n,1] div 4)+192,(cpal[n,2] div 4)+192);
                setrgbpalette(56+n,(cpal[n+8,0] div 4)+192,(cpal[n+8,1] div 4)+192,(cpal[n+8,2] div 4)+192);
            end;
        end;
     end;

     if mode=2 then begin
        cpal:=pal;
        for z:=0 to 255 do begin
            for c:=0 to 15 do begin
                     if cpal[c,0]>0 then cpal[c,0]:=cpal[c,0]-1;
                     if cpal[c,1]>0 then cpal[c,1]:=cpal[c,1]-1;
                     if cpal[c,2]>0 then cpal[c,2]:=cpal[c,2]-1;
            end;
            for n:=0 to 7 do begin
                setrgbpalette(n,(cpal[n,0] div 4)+192,(cpal[n,1] div 4)+192,(cpal[n,2] div 4)+192);
                setrgbpalette(56+n,(cpal[n+8,0] div 4)+192,(cpal[n+8,1] div 4)+192,(cpal[n+8,2] div 4)+192);
            end;
        end;
     end;

end;

procedure initbtn(n,x1,y1,w1,h1,bw1,ft1,fs1,dw1,pic1:integer;text1:string);
begin
     with btn[n] do begin
         x:=x1;
         y:=y1;
         w:=w1;
         h:=h1;
         bw:=bw1;
         ft:=ft1;
         fs:=fs1;
         dw:=dw1;
         text:=text1;
         pic:=pic1;
         rel:=0;
     end;
end;

procedure loadbmps;
begin
     loadbmp('pic\fcmd.bmp',1,13);
     loadbmp('pic\dir.bmp',2,13);
     loadbmp('pic\comp.bmp',3,13);
     loadbmp('pic\cbx.bmp',4,13);
     loadbmp('pic\close.bmp',5,-1);
     loadbmp('pic\min.bmp',6,-1);
     loadbmp('pic\i_dir.bmp',7,15);
     loadbmp('pic\i_file.bmp',8,15);
     loadbmp('pic\i_txt.bmp',9,15);
     loadbmp('pic\i_exe.bmp',10,15);
     loadbmp('pic\i_exm.bmp',11,15);
     loadbmp('pic\i_pic.bmp',12,15);
     loadbmp('pic\up.bmp',14,13);
     loadbmp('pic\down.bmp',15,13);
     loadbmp('pic\left.bmp',16,13);
     loadbmp('pic\right.bmp',17,13);
     loadbmp('pic\plus.bmp',18,15);
     loadbmp('pic\minus.bmp',19,15);
     loadbmp('pic\vis.bmp',20,0);
     loadbmp('pic\vis1.bmp',21,-1);
     loadbmp('pic\vis2.bmp',22,0);
     loadbmp('pic\vis3.bmp',23,0);
     loadbmp('pic\vis4.bmp',24,0);
     loadbmp('pic\vis5.bmp',25,0);
     loadbmp('pic\vis6.bmp',26,0);
     loadbmp('pic\vis7.bmp',27,0);
     loadbmp('pic\vis8.bmp',28,0);
     {drawbmp(1,1,1);}
end;

procedure initbuttons;
var n:integer;
begin
initbtn (1,2,457,60,20,1,4,1,0,1,'Пуск');
for n:=1 to 10 do
    initbtn(n+1,n*100-25,459,95,17,1,2,4,3,0,'');
end;

procedure drawborder(x,y,w,h:integer);
begin
          setcolor(8);
          line(x,y,x+w,y);
          line(x,y,x,y+h);
          setcolor(15);
          line(x+w,y+1,x+w,y+h);
          line(x+1,y+h,x+w,y+h);
          setcolor(0);
          rectangle(x-1,y-1,x+w+1,y+h+1);
end;


procedure drawbutton(nm,pressed:integer);
var bw,bh:integer;
var sx,sy:integer;
begin

     with btn[nm] do begin
          if rel=1 then sx:=awx else sx:=0;
          if rel=1 then sy:=awy else sy:=0;

          setfillstyle(1,7);
          bar(sx+x+1,sy+y+1,sx+x+w-1,sy+y+h-1);
          if pressed=0 then setcolor(15) else setcolor(8);
          line(sx+x,sy+y,sx+x+w,sy+y);
          line(sx+x,sy+y,sx+x,sy+y+h);
          if pressed=0 then setcolor(8) else setcolor(15);
          line(sx+x+w,sy+y+1,sx+x+w,sy+y+h);
          line(sx+x+1,sy+y+h,sx+x+w,sy+y+h);
          setcolor(0);
          rectangle(sx+x-1,sy+y-1,sx+x+w+1,sy+y+h+1);
          setcolor(0);
          settextstyle(ft,0,fs);
          bw:=0;

          if pic>0 then begin
             bw:=mbmp[pic].w;
             bh:=mbmp[pic].h;
             drawbmp(pic,sx+x+2+pressed,sy+pressed+y+(h-bh) div 2);
          end;
             outtextxy(sx+x+2+bw+pressed,sy+y+dw+pressed,text);

     end;
end;

function checkbutton(nm:integer):integer;
var xm,ym,bm:word;rez:integer;
var sx,sy:integer;
begin
     rez:=0;
     getmouse (xm,ym,bm);
     with btn[nm] do begin
     if rel=1 then sx:=awx else sx:=0;
     if rel=1 then sy:=awy else sy:=0;
         if bm=1 then
            if (xm>x+sx) and (ym>y+sy) and (xm<(x+w+sx)) and (ym<(y+h+sy)) then begin
               hide;
               drawbutton(nm,1);
               show;
               while bm=1 do
                     getmouse(xm,ym,bm);
               if (xm>x+sx) and (ym>y+sy) and (xm<(x+w+sx)) and (ym<(y+h+sy)) then rez:=1;
               hide;
               drawbutton(nm,0);
               show;
            end;
     end;
     checkbutton:=rez;
end;


procedure drawform(x,y,w,h,i:integer;caption:string);
begin
          setfillstyle(1,7);
          bar(x,y,x+w,y+h);
          setcolor(7);
          line(x,y,x,y+h);line(x,y,x+w,y);
          setcolor(15);
          line(x+1,y+1,x+1,y+h-1);line(x+1,y+1,x+w-1,y+1);
          setcolor(0);
          line(x+w,y+h,x+1,y+h);line(x+w,y+h,x+w,y+1);
          setcolor(8);
          line(x+w-1,y+h-1,x+2,y+h-1);line(x+w-1,y+h-1,x+w-1,y+2);
          setfillstyle(1,1);
          bar(x+3,y+3,x+w-3,y+20);
          settextstyle(0,0,0);
          setcolor(8); outtextxy(x+23,y+7,caption);
          setcolor(15); outtextxy(x+25,y+9,caption);
          if i>0 then drawbmp(i,x+5,y+3);
          drawbmp (4,x+w-53,y+4);
end;

procedure invert (x,y,w,h:integer);
var pimg:pointer;
var is:integer;
begin
     is:=imagesize(x,y,x+w,y+h);
     getmem (pimg,is);
     getimage (x,y,x+w,y+h,pimg^);
     putimage (x,y,pimg^,notput);
     freemem (pimg,is);
end;

function chmenu(x,y:integer):integer;
var n,m,w,h,lm:integer;
var xm,ym,bm:word;
var is:integer;img:pointer;
const strsz=15;
begin

          w:=100;h:=6+strsz*allmenu;
          is:=imagesize(x,y,x+w,y+h);
          getmem(img,is);
          bm:=1;
          while bm=1 do getmouse(xm,ym,bm);
          hide;
          getimage(x,y,x+w,y+h,img^);

          setfillstyle(1,7);
          bar(x,y,x+w,y+h);
          setcolor(7);
          line(x,y,x,y+h);line(x,y,x+w,y);
          setcolor(15);
          line(x+1,y+1,x+1,y+h-1);line(x+1,y+1,x+w-1,y+1);
          setcolor(0);
          line(x+w,y+h,x+1,y+h);line(x+w,y+h,x+w,y+1);
          setcolor(8);
          line(x+w-1,y+h-1,x+2,y+h-1);line(x+w-1,y+h-1,x+w-1,y+2);
          setcolor(0);
          settextstyle(2,0,4);
          for n:=1 to allmenu do
             if menu[n]<>'-' then
                outtextxy(x+10,y+6+strsz*(n-1),menu[n])
             else begin
                  setcolor(15);
                line(x+10,y+9+strsz*(n-1),x+90,y+9+strsz*(n-1));
                setcolor(8);
                line(x+10,y+8+strsz*(n-1),x+90,y+8+strsz*(n-1));
                setcolor(0);
             end;
             getmouse(xm,ym,bm);
          show;
          lm:=0;
          while bm=0 do begin
             getmouse(xm,ym,bm);
             m:=((ym-y) div strsz);
             if (ym-y)>0 then m:=m+1;
             if xm<x then m:=0;
             if xm>x+100 then m:=0;
             if (lm<>m) and (m>0) and (m<=allmenu) then begin
                 hide;
                  if lm>0 then invert (x+3,y+(lm-1)*strsz+3,94,strsz-2);
                  invert (x+3,y+(m-1)*strsz+3,94,strsz-2);
                 show;
                 lm:=m;
             end;
          end;
          hide;
          putimage(x,y,img^,0);
          freemem(img,is);
          show;
          if (m>0) and (m<=allmenu) then chmenu:=m else chmenu:=-1;
end;

procedure startgraph;
var d,m:integer;
begin
     d:=detect;
     d:=VGA;m:=VGAhi;
     initgraph(d,m,startdir);
     {setrgbpalette(3,0,0,192);}
end;

procedure defwindows;
var n:integer;
begin
     wnd[1].x:=70;
     wnd[1].y:=30;
     wnd[1].w:=430;
     wnd[1].h:=400;
     wnd[1].caption:='Mouse Commander';
     wnd[1].icon:=1;
     wnd[2].x:=300;
     wnd[2].y:=10;
     wnd[2].w:=300;
     wnd[2].h:=350;
     wnd[2].icon:=2;
     wnd[2].caption:='Просмотр';
     wnd[3].x:=170;
     wnd[3].y:=200;
     wnd[3].w:=300;
     wnd[3].h:=100;
     wnd[3].icon:=1;
     wnd[3].caption:='Сообщение';
     wnd[4].x:=170;
     wnd[4].y:=200;
     wnd[4].w:=150;
     wnd[4].h:=50;
     wnd[4].icon:=1;
     wnd[4].caption:='Копирование...';
     wnd[5].x:=300;
     wnd[5].y:=100;
     wnd[5].w:=300;
     wnd[5].h:=220;
     wnd[5].icon:=20;
     wnd[5].caption:='Виселица';
     for n:=1 to 10 do begin
         wnd[n].wc1:=nil;
         wnd[n].wc2:=nil;
         wnd[n].bc1:=nil;
         wnd[n].bc2:=nil;
         wnd[n].active:=0;
     end;
end;

procedure drawtaskbar;
var lw,n,wn,h,m,s,ss:word;bs:integer;
begin
setfillstyle(1,7);
bar(0,455,639,479);
setcolor(15);
line(0,455,639,455);
setcolor(7);
line(0,454,639,454);
gettime(h,m,s,ss);
drawbutton(1,0);
{drawbutton(595,457,1,stri(h)+':'+stri(m));}
bs:=0;wn:=1;
for n:=1 to 10 do begin
    if n=wndpos[allwnd] then bs:=1 else bs:=0;
    if wnd[n].active=1 then begin
        btn[wn+1].text:=wnd[n].caption;
        drawbutton(wn+1,bs);
        wn:=wn+1;
    end;
end;
end;

procedure getpic(x,y,w,h:integer;var p1,p2:pointer;var s1,s2:word);
var is:word;
begin
     if p1<>nil then freemem(p1,s1);
     if p2<>nil then freemem(p2,s2);
     s1:=0;s2:=0;p1:=nil;p2:=nil;

     is:=imagesize(x,y,x+w,y+h);
     if is>0 then begin
        getmem(p1,is);
        getimage(x,y,x+w,y+h,p1^);
        s1:=is;
     end
     else begin
        s1:=imagesize(x,y,x+w,y+(h div 2));
        s2:=imagesize(x,y+(h div 2),x+w,y+h);
        getmem(p1,s1);
        getmem(p2,s2);
        getimage(x,y,x+w,y+(h div 2),p1^);
        getimage(x,y+(h div 2),x+w,y+h,p2^);
     end;
end;

procedure putpic(x,y,h:integer;p1,p2:pointer);
begin
     putimage (x,y,p1^,0);
     if p2<>nil then putimage(x,y+(h div 2),p2^,0);
end;

procedure showwindow(wn,noform:integer);
var lw,x1,y1,w1,h1,i:integer;
begin
hide;
if allwnd>0 then begin
   with wnd[wndpos[allwnd]] do
        getpic(x,y,w,h,wc1,wc2,ws1,ws2);
end;
x1:=wnd[wn].x;
y1:=wnd[wn].y;
w1:=wnd[wn].w;
h1:=wnd[wn].h;
wnd[wn].active:=1;
getpic(x1,y1,w1,h1,wnd[wn].bc1,wnd[wn].bc2,wnd[wn].bs1,wnd[wn].bs2);
allwnd:=allwnd+1;
wndpos[allwnd]:=wn;
i:=wnd[wn].icon;
if noform=0 then drawform(x1,y1,w1,h1,i,wnd[wn].caption);
needinit:=wn;
drawtaskbar;
show;
end;

procedure closewindow;
var wn:integer;
begin
     hide;
     wn:=wndpos[allwnd];
     putpic(wnd[wn].x,wnd[wn].y,wnd[wn].h,wnd[wn].bc1,wnd[wn].bc2);
     freemem(wnd[wn].bc1,wnd[wn].bs1);
     if wnd[wn].bc2<>nil then freemem(wnd[wn].bc2,wnd[wn].bs2);
     if wnd[wn].wc1<>nil then freemem(wnd[wn].wc1,wnd[wn].ws1);
     if wnd[wn].wc2<>nil then freemem(wnd[wn].wc2,wnd[wn].ws2);
     wnd[wn].bc1:=nil;
     wnd[wn].bc2:=nil;
     wnd[wn].wc1:=nil;
     wnd[wn].wc2:=nil;
     wndpos[allwnd]:=0;
     wnd[wn].active:=0;
     allwnd:=allwnd-1;
     drawtaskbar;
     show;
end;

procedure setactive(wn:integer);
var n,wf,wp,is:integer;
begin
n:=10;
hide;
with wnd[wndpos[allwnd]] do getpic (x,y,w,h,wc1,wc2,ws1,ws2);
while wndpos[n]<>wn do begin
      if wndpos[n]>0 then
         with wnd[wndpos[n]] do putpic (x,y,h,bc1,bc2);
      n:=n-1;
end;
with wnd[wndpos[n]] do putpic (x,y,h,bc1,bc2);

for n:=1 to allwnd do if wndpos[n]=wn then wf:=n;
wndpos[wf]:=wndpos[allwnd];
wndpos[allwnd]:=wn;

for n:=wf to allwnd do
    with wnd[wndpos[n]] do begin
    getpic (x,y,w,h,bc1,bc2,bs1,bs2);
    putpic (x,y,h,wc1,wc2);
    end;
drawtaskbar;
end;

procedure controlwindows;
var n,xm,ym,bm,sw:word;
begin
     n:=allwnd;
     sw:=0;
     getmouse (xm,ym,bm);
     if bm=1 then begin
         while n>0 do begin
            with wnd[wndpos[n]] do
                 if (xm>x) and (xm<(x+w)) and (ym>y) and (ym<(y+h)) then begin
                    sw:=wndpos[n];
                    n:=1;
                 end;
            n:=n-1;
        end;
     if (sw>0) and (sw<>wndpos[allwnd]) then begin
        setactive (sw);
     end;
     end;
     show;
end;

procedure movewindows;
var aw,xm,ym,bm,xp,yp:word;
begin
     getmouse(xm,ym,bm);
     aw:=wndpos[allwnd];
     with wnd[aw] do
          if (xm>x) and (xm<(x+w-60)) and (ym>y) and (ym<(y+15)) and (bm=1) then begin
             while bm=1 do
                   getmouse(xp,yp,bm);
             xp:=xp-xm;
             yp:=yp-ym;
             if (abs(xp)>2) or (abs(yp)>2) then begin
             hide;
             getpic(x,y,w,h,wc1,wc2,ws1,ws2);
             putpic(x,y,h,bc1,bc2);
             x:=x+xp;
             y:=y+yp;
             if x<0 then x:=0;
             if y<0 then y:=0;
             if (x+w)>639 then x:=639-w;
             if (y+h)>450 then y:=450-h;
             getpic(x,y,w,h,bc1,bc2,bs1,bs2);
             putpic(x,y,h,wc1,wc2);
             show;
             end;
          end;
end;

procedure controlbox;
var aw,xm,ym,bm:word;
begin
     getmouse(xm,ym,bm);
     aw:=wndpos[allwnd];
     with wnd[aw] do
          if (xm>(x+w-20)) and (xm<(x+w-4)) and (ym>(y+3)) and (ym<(y+19)) and (bm=1) then begin
          hide;
          drawbmp(5,x+w-20,y+3);
          show;
          while bm=1 do getmouse(xm,ym,bm);
          closewindow;
          end;
end;

procedure checktaskbar;
var n,fw,wn,cbrez,i:integer;
var xm,ym,bm:word;
begin
     fw:=0;wn:=1;
     for n:=1 to 10 do begin
     if wnd[n].active=1 then begin
        wn:=wn+1;
        if checkbutton(wn)=1 then
           fw:=n;
     end;
     end;

     if (fw>0) and (fw<>wndpos[allwnd]) then
     setactive(fw);

     if checkbutton(1)=1 then begin
        menu[1]:='Игра Виселица';
        menu[2]:='Mouse Commander';
        menu[3]:='Выход';
        allmenu:=3;
        i:=chmenu(1,405);
        bm:=1;
        while bm=1 do getmouse(xm,ym,bm);
        if (i=1) and (wnd[5].active=0) then showwindow(5,0);
        if (i=2) and (wnd[1].active=0) then showwindow(1,0);
        if (i=3) then exitfl:=1;
     end;
end;

procedure freelist(nm:integer);
var n:integer;
begin
n:=0;
cfile:=files[nm];
while cfile<>nil do begin
      if cfile^.prev<>nil then dispose(cfile^.prev);
      if cfile^.next=nil then
         begin
         dispose(cfile);
         cfile:=nil;
         end
      else
         cfile:=cfile^.next;
      {n:=n+1;}
end;
end;

procedure loadcdir(nm:integer);
var frez:searchrec;
var cprev:pft;
var i:integer;
var lname:string;
begin
     freelist(nm);
     allfile[nm]:=1;
     new(files[nm]);
     cfile:=files[nm];
     cfile^.name:='.';
     cfile^.capt:='.';
     cfile^.prev:=nil;
     cfile^.adir:=true;
     cfile^.ahd:=false;
     cfile^.aro:=false;
     cfile^.index:=1;
     cfile^.ext:='';
     doserror:=0;
     findfirst('*.*',anyfile-volumeid,frez);
     if (frez.name='.') then
        findnext(frez);
     while doserror=0 do begin
          if (frez.attr and directory)=directory then begin
          allfile[nm]:=allfile[nm]+1;
          new(cfile^.next);
          cprev:=cfile;
          cfile:=cfile^.next;
          cfile^.prev:=cprev;
          cfile^.name:=frez.name;
          cfile^.capt:=frez.name;
          if (lfn=1) and (frez.name<>'..') then begin
             lname:=getlfn(frez.name);
             if length(lname)>30 then lname:=copy(lname,1,28)+'...';
             if lname<>'' then cfile^.capt:=lname;
          end;

          cfile^.adir:=true;
          cfile^.index:=allfile[nm];
          cfile^.ext:='';
          {write (frez.name);}
          end;
          findnext(frez);
     end;
     doserror:=0;
     findfirst('*.*',anyfile-directory-volumeid,frez);
     while doserror=0 do begin
          allfile[nm]:=allfile[nm]+1;
          new(cfile^.next);
          cprev:=cfile;
          cfile:=cfile^.next;
          cfile^.prev:=cprev;
          cfile^.name:=frez.name;
          cfile^.capt:=frez.name;
          if (lfn=1) and (frez.name<>'.') then begin
             lname:=getlfn(frez.name);
             if length(lname)>30 then lname:=copy(lname,1,28)+'...';
             if lname<>'' then cfile^.capt:=lname;
          end;
          i:=pos('.',frez.name);
          if i>0 then cfile^.ext:=copy(frez.name,i+1,3) else cfile^.ext:='';
          cfile^.adir:=false;
          cfile^.index:=allfile[nm];
          {writeln (frez.name);}
          findnext(frez);
     end;
     cfile^.next:=nil;
     {writeln(allfile[1]);}

end;
procedure scrcopy (x,y,w,h,dx,dy:integer);
var pimg:pointer;
var is:integer;
begin
     is:=imagesize(x,y,x+w,y+h);
     getmem (pimg,is);
     getimage (x,y,x+w,y+h,pimg^);
     putimage (x+dx,y+dy,pimg^,0);
     freemem (pimg,is);
end;



procedure selectfile (tab,state:integer);
var xp,yp,n:integer;
begin
n:=fmsel[tab]^.index-fmpos[tab]^.index;
xp:=awx+10+(tab-1)*210;
yp:=awy+fmtaby;

if (n>=0) and (n<fmpagesize) then
   invert (xp+3,1+yp+fmstroke*n,190,fmstroke-1);
end;

procedure drawfile(x,y:integer;pfile:pft);
var pic:integer;
var ext:string;
begin
setcolor(0);
settextstyle(2,0,4);
setfillstyle(1,15);
bar (x,y-1,x+190,y+fmstroke-2);
outtextxy (x+15,y-3,pfile^.capt);
pic:=8;
if pfile^.adir=true then pic:=7;
ext:=pfile^.ext;
if (ext='EXE') or (ext='BAT') or (EXT='COM') then pic:=10;
if (ext='TXT') or (ext='INI') or (ext='PAS') then pic:=9;
if (ext='BMP') then pic:=12;
drawbmp (pic,x+1,y-2);
end;

procedure drawlist(nm:integer);
var n,xp,yp:integer;
begin
xp:=awx+10+(nm-1)*210;
yp:=awy+fmtaby;
hide;
setfillstyle(1,15);
bar(xp+1,yp+1,xp+199,yp+304);
drawborder(xp,yp,200,305);
cfile:=fmpos[nm];
n:=0;
while (cfile<>nil) and (n<fmpagesize) do begin
      drawfile (xp+5,yp+fmstroke*n+3,cfile);
      cfile:=cfile^.next;
      n:=n+1;
end;
show;
end;

procedure moveselect(direct:integer);
var np,n:integer;
var pimg:pointer;
var pfile:pft;
var xp,yp:integer;
begin
hide;
     xp:=awx+10+(fmtab-1)*210;
     yp:=awy+fmtaby;

     if (fmsel[fmtab]^.index>1) and (direct=-1) or ((fmsel[fmtab]^.index<allfile[fmtab]) and (direct=1)) then begin
          np:=-fmpos[fmtab]^.index+fmsel[fmtab]^.index+direct;
          if (np>=0) and (np<fmpagesize) then begin
             selectfile(fmtab,0);
             if direct=-1 then fmsel[fmtab]:=fmsel[fmtab]^.prev;
             if direct=+1 then fmsel[fmtab]:=fmsel[fmtab]^.next;
             selectfile(fmtab,1);
          end;
          if (np>=fmpagesize) then begin
             selectfile(fmtab,0);
             fmpos[fmtab]:=fmpos[fmtab]^.next;
             scrcopy (xp,yp+fmstroke+1,200,fmstroke*(fmpagesize-1)+1,0,-fmstroke);
             {drawlist(fmtab);}
             fmsel[fmtab]:=fmsel[fmtab]^.next;
             pfile:=fmpos[fmtab];
             for n:=1 to fmpagesize do pfile:=pfile^.next;
             drawfile (xp+5,yp+fmstroke*(fmpagesize-1)+3,fmsel[fmtab]);
             selectfile(fmtab,1);
          end;
          if (np<0) then begin
             selectfile(fmtab,0);
             fmpos[fmtab]:=fmpos[fmtab]^.prev;
             scrcopy (xp,yp+1,200,fmstroke*(fmpagesize-1),0,+fmstroke);
             fmsel[fmtab]:=fmsel[fmtab]^.prev;
             pfile:=fmpos[fmtab];
             drawfile (xp+5,yp+3,fmpos[fmtab]);
             selectfile(fmtab,1);
          end;
     end;
show;
end;

procedure switchpage(direct:integer);
var m,n,np:integer;
begin
hide;
np:=fmpos[fmtab]^.index+fmpagesize*direct;
if (np>=0) and (np<allfile[fmtab]) then begin
   selectfile(fmtab,0);
   for n:=1 to fmpagesize do begin
       if direct=+1 then fmpos[fmtab]:=fmpos[fmtab]^.next;
       if direct=-1 then fmpos[fmtab]:=fmpos[fmtab]^.prev;
   end;
   drawlist(fmtab);
   m:=0;
   if direct=1 then
   while (m<fmpagesize) and (fmsel[fmtab]^.next<>nil) do begin
       fmsel[fmtab]:=fmsel[fmtab]^.next;
       m:=m+1;
   end;
   if direct=-1 then
   while m<fmpagesize do begin
       fmsel[fmtab]:=fmsel[fmtab]^.prev;
       m:=m+1;
   end;

   selectfile(fmtab,1);
end;
if np<0 then begin
   selectfile(fmtab,0);
   fmpos[fmtab]:=files[fmtab];
   fmsel[fmtab]:=files[fmtab];
   drawlist(fmtab);
   selectfile(fmtab,1);
end;
show;
end;

procedure changedir(ndir:string);
{var ndir:string;}
begin
hide;
     selectfile(fmtab,0);

     chdir(ndir);
     getdir(0,fmpath[fmtab]);
     loadcdir(fmtab);
     fmpos[fmtab]:=files[fmtab];
     fmsel[fmtab]:=files[fmtab];
     drawlist(fmtab);
     selectfile(fmtab,1);
show;
end;

procedure runexe;
var n:integer;
begin
hide;
with wnd[wndpos[allwnd]] do getpic (x,y,w,h,wc1,wc2,ws1,ws2);
cleardevice;
closegraph;
exec (fmsel[fmtab]^.name,'');
startgraph;
initmouse;
hide;
setpalette(0);
drawtaskbar;
for n:=1 to allwnd do
    with wnd[wndpos[allwnd]] do putpic (x,y,h,wc1,wc2);
show;
end;

procedure runview;
begin
if fmsel[fmtab]^.adir=false then begin

if length(fmpath[fmtab])<>3 then
   vwfile:=fmpath[fmtab]+'\'+fmsel[fmtab]^.name
else
    vwfile:=fmpath[fmtab]+fmsel[fmtab]^.name;

vwext:=fmsel[fmtab]^.ext;

if wnd[2].active=0 then
   showwindow(2,0)
   else begin
   needinit:=2;
   setactive(2);
   end;
end;
end;

procedure initfilemanager;
var td:longint;
var n,m:integer;
begin
     m:=0;
     for n:=1 to 23 do
         if diskfree(n)>-1 then begin
                  with btn[60-m] do begin
                  h:=12;bw:=1;
                  w:=20;dw:=2;
                  y:=40;
                  x:=10+25*m;
                  fs:=0;ft:=0;
                  pic:=0;text:=chr(ord('A')+n-1)+':';
                  rel:=1;
                  {m:=m+1;}
                  end;
                  drawbutton(60-m,0);
                  m:=m+1;
                  end;
                 alldrive:=m;

     for n:=1 to 5 do with btn[12+n] do begin
         y:=375;dw:=5;bw:=1;
         x:=5+85*(n-1);
         h:=18;w:=80;
         fs:=4;ft:=2;
         pic:=0;rel:=1;
     end;
     settextstyle(0,0,1);
     outtextxy(awx+10,awy+25,'Файл');
     outtextxy(awx+50,awy+25,'Вид');
     outtextxy(awx+90,awy+25,'Справка');
     btn[13].text:='F3 Просмотр';
     btn[14].text:='F5 Копировать';
     btn[15].text:='F6 Переимен.';
     btn[16].text:='F7 Нов. папка';
     btn[17].text:='F8 Удалить';
     for n:=13 to 17 do drawbutton(n,0);
     fmtab:=1;
     getdir(0,fmpath[1]);
     getdir(0,fmpath[2]);
     loadcdir(1);loadcdir(2);
     fmpos[1]:=files[1];
     fmpos[2]:=files[2];
     fmsel[1]:=fmpos[1];
     fmsel[2]:=fmpos[2];
     drawlist(1);
     drawlist(2);
     selectfile(1,1);
     plainrefr:=0;
end;



procedure fdelete;
var fl:file;
begin
if fmsel[fmtab]^.adir=true then
   begin
   if (fmsel[fmtab]^.name<>'.') and (fmsel[fmtab]^.name<>'..') then
      rmdir(fmsel[fmtab]^.name);
   end
   else begin
        assign(fl,fmsel[fmtab]^.name);
        erase(fl);
   end;
   changedir('.');
end;

procedure startrename;
var fl:file;
begin
     msinp:=1;
     mstext:='Введите новое имя (стандарт 8.3):';
     msevnt:=1;
     showwindow(3,0);
end;
procedure startnewdir;
var fl:file;
begin
     msinp:=1;
     mstext:='Введите имя папки (стандарт 8.3):';
     msevnt:=2;
     showwindow(3,0);
end;

procedure fcopy;
var f1,f2:file;
var p1,p2,fn:string;
var tmp:array[0..127] of char;
var nr,nw:integer;
begin
     showwindow(4,0);
     p1:=fmpath[fmtab];
     p2:=fmpath[3-fmtab];
     if length(p1)=3 then p1:=copy(p1,1,2);
     if length(p2)=3 then p2:=copy(p2,1,2);
     if fmsel[fmtab]^.adir=false then begin
        p1:=p1+'\'+fmsel[fmtab]^.name;
        p2:=p2+'\'+fmsel[fmtab]^.name;
        if p1<>p2 then begin
            assign(f1,p1);
            assign(f2,p2);
            reset(f1,128);
            rewrite(f2,128);
            if ioresult=0 then begin
                repeat
                      blockread(f1,tmp,1,nr);
                      blockwrite(f2,tmp,1,nw)
                until (nr=0);
            end;
        end;
     end;
     closewindow;
     selectfile(fmtab,0);
     if fmtab=1 then fmtab:=2 else fmtab:=1;
     chdir (fmpath[fmtab]);
     selectfile(fmtab,1);
     changedir('.');
end;

procedure doevent;
var fl:file;
begin
     case msevnt of
          1:begin
                 assign(fl,fmsel[fmtab]^.name);
                 rename(fl,msanswer);
                 plainrefr:=1;
          end;
          2:begin
                 mkdir(msanswer);
                 plainrefr:=1;
          end;
     end;
     msevnt:=0;
     needevent:=0;
{     if ioresult}
end;

procedure workfilemanager;
var n,rez:integer;
var xm,ym,bm:word;
begin
     for n:=60 downto 60-alldrive do
         if checkbutton(n)=1 then begin
            changedir(btn[n].text+'\');
         end;
     if checkbutton(13)=1 then runview;
     if checkbutton(14)=1 then fcopy;
     if checkbutton(15)=1 then startrename;
     if checkbutton(16)=1 then startnewdir;
     if checkbutton(17)=1 then fdelete;
     case key2 of
     #72: moveselect(-1);
     #80: moveselect(+1);
     #75,#73: switchpage(-1);
     #77,#81: switchpage(+1);
     #61:runview;
     #63:fcopy;
     #64:startrename;
     #65:startnewdir;
     #66:fdelete;
     end;
     case key1 of
     #9:  begin
          selectfile(fmtab,0);
          if fmtab=1 then fmtab:=2 else fmtab:=1;
          chdir (fmpath[fmtab]);
          selectfile(fmtab,1);
          end;
     #13: begin
          if fmsel[fmtab]^.adir=true then changedir(fmsel[fmtab]^.name);
          if fmsel[fmtab]^.ext='EXE' then runexe;
          if fmsel[fmtab]^.ext='COM' then runexe;
          if fmsel[fmtab]^.ext='BAT' then runexe;
          {if}
          end;
     end;
     getmouse(xm,ym,bm);
     if (ym>awy+25) and (ym<awy+35) and (bm=1) then begin
        if (xm>awx+10) and (xm<awx+40) then begin
            menu[1]:='Запуск';
            menu[2]:='Просмотр';
            menu[3]:='-';
            menu[4]:='Виселица';
            menu[5]:='Выход';
            allmenu:=5;
            rez:=chmenu(awx+5,awy+35);
            bm:=1;
            while bm=1 do getmouse(xm,ym,bm);
            if rez=1 then runexe;
            if rez=2 then runview;
            if rez=5 then closewindow;
            if (rez=4) and (wnd[5].active=0) then showwindow(5,0);
        end;
        if (xm>awx+50) and (xm<awx+80) then begin
            menu[1]:='Обновить';
            menu[2]:='Выбрать папку';
            allmenu:=2;
            rez:=chmenu(awx+45,awy+35);
            bm:=1;
            while bm=1 do getmouse(xm,ym,bm);
            if rez=1 then plainrefr:=1;

        end;
                if (xm>awx+90) and (xm<awx+140) then begin
            menu[1]:='О программе';
            allmenu:=1;
            rez:=chmenu(awx+85,awy+35);
            bm:=1;
            while bm=1 do getmouse(xm,ym,bm);
            if (rez=1) and (wnd[3].active=0) then begin
                msinp:=0;
                mstext:='(c) Игорь Кошелев, 2-6 июня 2006г.';
                showwindow(3,0);
            end;

        end;
     end;
     if plainrefr=1 then begin
        changedir('.');
        plainrefr:=0;
     end;
end;

procedure workviewer;
var bx,by,newmode,chng:integer;
begin
     newmode:=0;chng:=0;
     case key2 of
     #72: if vwdy>0 then begin vwdy:=vwdy-1;chng:=1; end;
     #80: begin vwdy:=vwdy+1;chng:=1;end;
     end;
     if checkbutton(18)=1 then newmode:=1;
     if checkbutton(19)=1 then newmode:=2;
     if checkbutton(20)=1 then newmode:=3;
     if (checkbutton(21)=1) and (vwdx>0) then begin chng:=1; vwdx:=vwdx-1; end;
     if checkbutton(22)=1 then begin chng:=1; vwdx:=vwdx+1; end;
     if (checkbutton(23)=1) and (vwdy>0) then begin chng:=1; vwdy:=vwdy-1; end;
     if checkbutton(24)=1 then begin chng:=1; vwdy:=vwdy+1; end;
     if checkbutton(25)=1 then begin chng:=1; vwsz:=vwsz+1; end;
     if (checkbutton(26)=1) and (vwsz>1) then begin chng:=1; vwsz:=vwsz-1; end;
     if newmode<>vwmode then begin
        if newmode=3 then begin
           getbmpinfo(vwfile,bx,by);
           if bx=-1 then newmode:=2 else
              begin
                   if by>bx then bx:=by;
                   vwsz:=(bx div 280)+1;
                   vwpis:=bx div vwsz;
                   setfillstyle(1,15);
                   bar(awx+11,awy+61,awx+290,awy+340);
                   viewbmp(vwfile,awx+11,awy+61,0,0,vwsz);
                   vwmode:=3;vwdx:=0;vwdy:=0;
              end;
        end;
        if (newmode=2) or (newmode=1) then begin
           vwdx:=0;vwdy:=0;
           vwmode:=newmode;
           chng:=1;
        end;
      end;
        if chng=1 then begin
           setfillstyle(1,15);
           bar(awx+11,awy+61,awx+290,awy+340);
        end;

        if (vwmode=3) and (chng=1) then
          viewbmp(vwfile,awx+11,awy+61,200*vwdx,200*vwdy,vwsz);

        if (vwmode=2) and (chng=1) then
           viewbin(vwfile,awx+11,awy+61,vwdy);

        if (vwmode=1) and (chng=1) then
           viewtxt(vwfile,awx+11,awy+61,vwdy);

end;

procedure initviewer;
var n,bx,by:integer;
begin
for n:=1 to 3 do with btn[17+n] do begin
         y:=30;dw:=5;bw:=1;
         x:=15+40*(n-1);
         h:=18;w:=35;
         fs:=4;ft:=2;
         pic:=0;rel:=1;
     end;
for n:=1 to 6 do with btn[20+n] do begin
         y:=30;dw:=5;bw:=1;
         x:=150+23*(n-1);
         h:=18;w:=18;
         fs:=1;ft:=0;
         pic:=0;rel:=1;
     end;
     btn[18].text:='Текст';
     btn[19].text:='Байты';
     btn[20].text:=' BMP';

     btn[21].text:='';
     btn[21].pic:=16;

     btn[22].text:='';
     btn[22].pic:=17;

     btn[23].text:='';
     btn[23].pic:=14;

     btn[24].text:='';
     btn[24].pic:=15;

     btn[25].text:='';
     btn[25].pic:=19;

     btn[26].text:='';
     btn[26].pic:=18;
     for n:=18 to 26 do drawbutton(n,0);
     setfillstyle(1,15);
     bar(awx+11,awy+61,awx+288,awy+340);
     drawborder (awx+10,awy+60,280,280);

     vwmode:=2;
     vwsz:=1;vwdx:=0;vwdy:=0;
     if vwext='INI' then vwmode:=1;
     if vwext='TXT' then vwmode:=1;
     if vwext='PAS' then vwmode:=1;
     if vwext='BAS' then vwmode:=1;
     if vwext='BMP' then begin
        vwmode:=3;
        getbmpinfo(vwfile,bx,by);
        if bx=-1 then vwmode:=2;
     end;

     if vwmode=1 then viewtxt(vwfile,awx+11,awy+61,0);
     if vwmode=2 then viewbin(vwfile,awx+11,awy+61,0);

     if vwmode=3 then begin
         if by>bx then bx:=by;
           vwsz:=(bx div 280)+1;
           vwpis:=bx div vwsz;
           viewbmp(vwfile,awx+11,awy+61,0,0,vwsz);
     end;

end;

procedure initmsg;
begin
with btn[30] do begin
     x:=140;w:=40;
     y:=80;h:=15;
     text:=' ОК';
     dw:=5;bw:=1;
     ft:=0;fs:=1;
     rel:=1;
     end;
settextstyle(0,0,1);
setcolor(0);
hide;
outtextxy(awx+10,awy+30,mstext);
drawbutton(30,0);
msready:=0;
msanswer:='';
if msinp=1 then begin
setfillstyle(1,15);hide;
bar(awx+21,awy+46,awx+279,awy+64);
drawborder(awx+20,awy+45,260,20);
end;
show;
notasking:=1;
end;

procedure workmsg;
var i,n:integer;
begin
     i:=checkbutton(30);
     settextstyle(2,0,4);
     setcolor(0);
     if msinp=1 then
     case key1 of
        #40..#122,#128..#175:
            if length(msanswer)<40 then begin
            msanswer:=msanswer+key1;
            hide;
            outtextxy(awx+25,awy+50,msanswer);
            show;
            end;
        #8:
        if length(msanswer)>0 then begin
            setfillstyle(1,15);hide;
            bar(awx+21,awy+46,awx+279,awy+64);
            msanswer:=copy(msanswer,1,length(msanswer)-1);
            outtextxy(awx+25,awy+50,msanswer);
            show;
        end;
     end;

     if key1=#13 then i:=1;
     if i=1 then begin
        notasking:=0;
        msready:=1;
        closewindow;
        doevent;
        msevnt:=0;
     end;
end;

procedure drawword;
var n,dx:integer;
begin
     hide;
     dx:=(300-vlen*30) div 2;
     for n:=1 to vlen do begin
         setfillstyle(1,15);
         bar (dx+5+awx+30*(n-1),awy+50,dx+awx+30*n,awy+75);
         drawborder(dx+5+awx+30*(n-1)+1,awy+51,23,23);
         settextstyle(1,0,3);
         setcolor(4);
         outtextxy(dx+7+awx+30*(n-1),awy+48,vtry[n]);
     end;
     show;
end;

procedure drawscore;
var sts:string;
begin
settextstyle(0,0,1);
setcolor(1);
case vwin of
1:sts:='Выиграли!!!';
0:sts:='Идет игра';
-1:sts:='Проиграли';
end;
case vmist of
4:sts:='Еле жив';
5:sts:='Почти...';
end;
hide;
setfillstyle(1,7);
bar(awx+10,awy+80,awx+150,awy+150);
outtextxy(awx+10,awy+90,'Угадано:'+stri(vvern));
outtextxy(awx+10,awy+110,'Ошибок :'+stri(vmist));
outtextxy(awx+10,awy+130,'Статус :'+sts);
show;
end;

procedure checkltr(ltr:char);
var pf,n:integer;
begin
     pf:=0;
     for n:=1 to vlen do
         if ltr=vword[n] then begin
            vtry[n]:=ltr;
            vword[n]:='+';
            vvern:=vvern+1;
            pf:=1;
         end;

         if pf=0 then begin
            vmist:=vmist+1;
            drawbmp(21+vmist,awx+180,awy+100);
            end
         else drawword;
         if vvern=vlen then vwin:=1;
         if vmist=6 then vwin:=-1;
         drawscore;
end;

procedure initvis;
var words:array[1..10] of string;
var vn,n:integer;
begin
randomize;
words[1]:='КОТЕНОК';
words[2]:='ПОПУГАЙ';
words[3]:='ПОРОСЕНОК';
words[4]:='КОЗЕЛ';
words[5]:='МЫШКА';
words[6]:='СОБАЧКА';
vn:=trunc(random(6))+1;
vword:=words[vn];
vlen:=length(vword);
vtry:='';

for n:=1 to vlen do vtry:=vtry+'-';
vmist:=0;vvern:=0;vwin:=0;
hide;
settextstyle(1,0,3);setcolor(0);
outtextxy(awx+10,awy+20,'Отгадайте животное:');
drawbmp (21,awx+160,awy+80);
show;
drawword;
drawscore;
end;

procedure workvis;
begin
     if (vwin=0) and (key1>='А') and (key1<='Я') then checkltr (key1);
end;

procedure initwindow(nm:integer);
begin
     awx:=wnd[nm].x;
     awy:=wnd[nm].y;
     if nm=1 then initfilemanager;
     if nm=2 then initviewer;
     if nm=3 then initmsg;
     if nm=5 then initvis;
     needinit:=0;
end;

procedure workwindow(nm:integer);
begin
     awx:=wnd[nm].x;
     awy:=wnd[nm].y;
     if nm=1 then workfilemanager;
     if nm=2 then workviewer;
     if nm=3 then workmsg;
     if nm=5 then workvis;
end;

procedure drawclock;
var h,m,s,ss:word;
begin
gettime(h,m,s,ss);
if lastmin<>m then begin
setfillstyle(1,7);
bar (580,459,629,474);
drawborder (580,458,50,18);
settextstyle(0,0,1);
gettime(h,m,s,ss);
outtextxy (588,465,stri(h)+':'+stri(m));
lastmin:=m;
end;
end;

begin
getdir(0,startdir);
startgraph;
loadpalette;
setpalette(-1);
viewbmp ('pic\logo.bmp',200,50,0,0,1);
delay(50000);delay(50000);delay(50000);delay(50000);
setpalette(1);
delay(50000);delay(50000);delay(50000);delay(50000);

setfillstyle(1,3);
floodfill(10,10,13);
setpalette(0);
loadbmps;
initmouse;
initbuttons;
defwindows;
hide;
needinit:=0;needevent:=0;msevnt:=0;
exitfl:=0;
{msinp:=1;
mstext:='Вопрос';}
showwindow(1,0);
drawtaskbar;
drawclock;
show;
while (key2<>'D') and (exitfl=0) do begin
if keypressed=true then begin
              key1:=readkey;
           if key1=#0 then key2:=readkey;        {f3-61}
           end
           else begin
                key1:=#0;key2:=#0;
           end;
      controlwindows;
      checktaskbar;
      movewindows;
      controlbox;
      drawclock;
      if needinit>0 then initwindow(needinit);
      {if needevent>0 then begin doevent;needevent:=0;end;}
      workwindow(wndpos[allwnd]);

end;
setpalette(2);
while allwnd>0 do closewindow;
closegraph;
freelist(1);
freelist(2);
chdir(startdir);
end.