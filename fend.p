program fend (input, output);
  {A "front end" to help get the constants just right for both nf6.p and nf3.p}
  {You can be liberal with the assignment of constants here. }
  {7-8-94: up to date for new nf3 and nf6}
  {8-29-94: works for nonconsecutive numbers}
  {2-3-95: bug in non-consecutive numbering routine fixed}

const r=2; {r=the max. number of traits}
      f=40;  {the max number of families}
      missing=-98; {Value in the dataset indicating missing phenotypic data
                    if your missing values are -99.00, then "missing" = -98}
      nmax=400; {maximum total # of individuals in the dataset, including
                 those missing data}
      pos=200; {r * largest family size to be safe}
      null=0;  {ID # for relatives not present in the input data}
      nf = 2;  {the max. number of fixed effects}
      p = 15;  {the maximum number of levels of fixed effects=r~nlevels}

  {The following commands must be issued prior to a run on a VAX:
    $ define sibships sibships
    $ define topend topend }


 type list = array[1..nf] of integer;
      Observation=record
                   ID:integer;
                   Father: integer;
                   Mother: integer;
                   NPS, NMS, FO, Famid: integer;
		   FixedVals: list;
                 end;  {Observation}
     Dataset=array[1..nmax] of Observation;
     Famset=array[1..nmax] of Observation;
     Famarray=array[1..f] of Famset;
     Measures = array[1..nmax,1..r] of real;
     Famphens = array[1..pos,1..p] of real;
     Fammat=array[1..f] of Famphens;
     Size=array[1..f] of integer;
     items= array [1..nf,1..p] of integer;
     charlist = array [1..r] of integer;

var  PresentData: Dataset;
     sibships: text;
     Topend: text;
     nchar, ntrunc, slevels, nfxfact :integer;
     newfam, I: integer;
     Families: Famarray;
     FamZ: Fammat;
     M, famnum: integer; {tot #, fam#, #types of comps estimable}
     Zmatrix:Measures;
     famsize, vert: Size;
     nfxlevels: list; {contains the true number of levels for each fixed factor}
     levels: items;

procedure Getphtypes(var Data:Dataset; var M: integer; var nchar:integer;
                     var Zmatrix: Measures; var slevels: integer;
		     var nfxlevels: list);

          {read the data from the input file. Each line of data is a record
          for an individual in the pedigree, containing, in order, an  ID
          number, the sire's ID, the dam's ID, the ID of the next paternal sib,
          and that of the next maternal sib
          (the values of relatives not present in the pedigree are assumed
          to be set at 0), followed by phenotypic values for an arbitrary
          number of traits in a consistent order.  (The value of a
          trait that is missing for a given individual is assumed to be -99.
          Both parents of individuals for which phenotypic data is available
          must be included in the pedigree, regardless of whether
          phenotypic information is available for them.)}

   var  TempID, TempFather, TempMother: integer;
        Pheno: real;
        J, K, L, which, nmobs:integer;
	already: boolean;
   begin
      slevels := 0;
      for K := 1 to nfxfact do begin
         nfxlevels[K] := 0;
         for L := 1 to p do
 	    levels[K,L] := -99;
	 end;
      M := 0;
      nmobs := 0;
      read (sibships,TempID);
      while not (TempID=null) do begin
         M :=M+1;
         if M > nmax then begin
          writeln ( ' The program is finding too many records of data: ' );
          writeln ( ' "nmax" is too small! ');
          halt;
         end;
         read (sibships, TempFather,TempMother);
         with Data[M] do begin
            ID := TempID ;
	    Father:=TempFather;
	    Mother:=TempMother;
            NPS := 0;
            NMS := 0;
            FO := 0;
            Famid := 0;
            for K := 1 to nfxfact do begin
               read (sibships,which);
               already := false;
               for L := 1 to nfxlevels[K] do
                  if (which=levels[K,L])
                  then begin
                   already := true;
                   FixedVals[K] := L;
                  end;
               if not already
               then begin
                  nfxlevels[K]:= nfxlevels[K] + 1;
                  FixedVals[K] := nfxlevels[K];
                  slevels := slevels + 1;
                   if slevels > p then begin
                    writeln ('the constant p is too low at the top of the program');
                    halt;
                   end;
                  levels[K,nfxlevels[K]] := which;
                  end;
               end; {K}
            end; {with}
         for J := 1 to nchar do begin
            read (sibships, Pheno);
            if Pheno > missing then nmobs := nmobs + 1;
            Zmatrix[M,J]:=Pheno;
            end;
         readln (sibships);
         read (sibships,TempID);
      end; {while not}
   readln (sibships);
   {true up the numbering.  The new parental ids are first set negative
    so that they will not be changed twice}
   for I := 1 to M do begin 
    if (Data[I].Father = 0) then begin
     {find progeny}
     for J := 1 to M do begin
      if Data[J].Father =  Data[I].ID then
       Data[J].Father := -I;
      if Data[J].Mother =  Data[I].ID then
       Data[J].Mother := -I;
     end; {J}
    end; {if founder}
   end; {I}
  {reset the parental id numbers positive}
   for I := 1 to M do begin 
    if not (Data[I].Father = 0) then begin
     Data[I].Father := -Data[I].Father;
     Data[I].Mother := -Data[I].Mother;
    end;
   end; {I}
   writeln ('The total number of records is',M);
   writeln ('The total number of non-missing observations is',nmobs);
   if (nfxfact < 1)
   then slevels := 1;
   slevels := nchar * slevels;
   if nfxfact > 1 then begin
    slevels := slevels - (nfxfact - 1);
    writeln (Topend,'nf =',nfxfact:5);
   end
   else writeln (Topend,'nf = 1');
   writeln (Topend, 'p =',slevels:5);
   end; {Getphtypes}

procedure FindGroupsN (var Data:Dataset; var M: integer);
   var I, J, Dad, Mom, Me : integer;
       matched1, matched2 : boolean;
   begin
      for I := 1 to M do begin
         Dad := Data[I].Father;
         Mom := Data[I].Mother;
         Me := I;
         if Dad > 0 
	 then begin
           if Data[Dad].FO = 0
           then Data[Dad].FO := Me;
  	   J := I;
	    matched1 := false;
	    repeat 
	       J := J + 1;
               if (Data[J].Father = Dad) or (Data[J].Mother = Dad)
	       then begin
	          Data[I].NPS := J;
	          matched1 := true;
	          end;
	    until matched1 or (J>M-1);
	    end;
         if Mom > 0 
	 then begin
            if Data[Mom].FO = 0
            then Data[Mom].FO := Me;
  	    J := I;
	    matched2 := false;
            repeat 
	       J := J + 1;
               if (Data[J].Father = Mom) or (Data[J].Mother = Mom)
	       then begin
	          Data[I].NMS := J;
	          matched2 := true;
	          end;
	    until matched2 or (J>M-1);
            end;
         end;
      end;

procedure Visit (var rel:Observation; family:integer);

      {Family designations are assigned to each individual, using all the
      information of relationships.}

   begin
      if rel.Famid = 0
      then begin
         rel.Famid := family;
         if (rel.FO > 0)
         then Visit (PresentData[rel.FO], family);
         if (rel.NPS > 0)
         then Visit (PresentData[rel.NPS], family);
         if (rel.NMS > 0)
         then Visit (PresentData[rel.NMS], family);
         if (rel.Father > 0)
         then Visit (PresentData[rel.Father], family);
         if (rel.Mother > 0)
         then Visit (PresentData[rel.Mother], family);
         end;
      end; {Visit}

procedure Check (I:integer; Data:Dataset; var y : integer);
   var Dad, Mom:integer;
   begin
      Dad := Data[I].Father;
      if Dad > null
      then y := Data[Dad].Famid;
      if (y=0)
      then begin
         Mom := Data[I].Mother;
         if Mom > null
         then y := Data[Mom].Famid;
	 end;
      end;


procedure Collecthem (var Data: Dataset; var Families: Famarray; 
                      var FamZ:Fammat; var famsize: Size);

        {Two arrays are built for each family.  One contains the pedigree
        info. (Families) and the other contains the phenotypes (FamZ).}
        {the sizes for the derivitive arrays are calculated and printed}

   var I, J, K, L, mom, dad, mfz: integer;
   var rfsibs,fsibs,hsibs,rhsibs : charlist;
   var mrfsibs,mfsibs,mrhsibs,mhsibs : integer;
   begin {Collecthem}
      mrhsibs := 0;
      mhsibs := 0;
      mrfsibs := 0;
      mfsibs := 0;
      mfz := 0;
      for I := 1 to famnum do begin
         L:=1;
         for K := 1 to M do begin
            if Data[K].Famid=I
            then begin
               Families[I][L]:=Data[K];
               for J := 1 to nchar do
                   FamZ[I][L,J] := Zmatrix[K,J];
               L := L+1;
               end;
            end;
         famsize[I] := L-1;
         writeln (Topend,'family',I,' has',famsize[I]);
          if mfz < famsize[I] then mfz := famsize[I];
          for J := 1 to famsize[I] do begin
         for L := 1 to nchar do begin
         rhsibs[L] := 0;
         rfsibs[L] := 0;
         hsibs[L] := 0;
         fsibs[L] := 0;
         end;
           mom := Families[I][J].Mother;
           dad := Families[I][J].Father;
             for K := 1 to famsize[I] do begin
if (mom > 0) and (dad > 0)
then begin
               if Families[I][K].Father = dad
   then begin
    for L := 1 to nchar do begin
     if (FamZ[I][K,L] > missing)
      then begin
      rhsibs[L] := rhsibs[L] + 1;
      hsibs[L] := hsibs[L] + 1;
      end;
    end;
      if Families[I][K].Mother = mom 
        then begin
    for L := 1 to nchar do begin
     if (FamZ[I][K,L] > missing)
      then begin
      rfsibs[L] := rfsibs[L] + 1;
      fsibs[L] := fsibs[L] + 1;
      end;
    end; {L}
       end; {if mom}
                 end {if dad} 
                 else begin
                 if Families[I][K].Mother = mom 
                 then begin
    for L := 1 to nchar do begin
     if (FamZ[I][K,L] > missing)
                then begin
                 rhsibs[L] := rhsibs[L] + 1;
                 hsibs[L] := hsibs[L] + 1;
                  end;
    end;
                  end;
                 end; {else}
               if Families[I][K].Father = mom 
   then begin
    for L := 1 to nchar do begin
     if (FamZ[I][K,L] > missing)
      then begin
      rhsibs[L] := rhsibs[L] + 1;
      end;
    end;
      if Families[I][K].Mother = dad 
        then begin
    for L := 1 to nchar do begin
     if (FamZ[I][K,L] > missing)
      then begin
      rfsibs[L] := rfsibs[L] + 1;
      end;
    end; {L}
                 end; {if mom} 
       end {if dad}
       else begin
      if Families[I][K].Mother = dad 
        then begin
    for L := 1 to nchar do begin
     if (FamZ[I][K,L] > missing)
        then begin
        rhsibs[L] := rhsibs[L] + 1;
        end;
    end;
        end;
      end; {else}
end;
          end; {K}
       for L := 1 to nchar do begin
        if rhsibs[L] > mrhsibs
        then mrhsibs := rhsibs[L];
        if hsibs[L] > mhsibs
        then mhsibs := hsibs[L];
        if rfsibs[L] > mrfsibs
        then mrfsibs := rfsibs[L];
        if fsibs[L] > mfsibs
        then mfsibs := fsibs[L];
       end; {L}
         end; {J}
         end; {I}
        writeln (Topend,'sibs=',mfz);
        writeln (Topend,'rhsibs=',mrhsibs);
        writeln (Topend,'fsibs=',mfsibs);
        writeln (Topend,'hsibs=',mhsibs);
        writeln (Topend,'rfsibs=',mrfsibs);
        writeln (Topend, 'nf3.p only needs rfsibs and rhsibs ');
       end; {Collecthem}

procedure Designit (FamZ: Fammat; var vert:Size);

    var I, J, g: integer;
        vertical, mvert : integer;
    begin
       mvert := 0;
       for g := 1 to famnum do begin
          vertical:=0;
          for I:=1 to famsize[g] do begin
            for J:=1 to nchar do begin
               if not (FamZ[g][I,J]<missing)
                then begin
                  vertical:=vertical+1;
 		  end; {if}
 	       end; {J}
             end; {I}
 	 vert[g] := vertical;
         writeln (Topend,'non-missing observations for family',g,':',vert[g]);
         if vert[g] = 0 then begin
            writeln ('Warning! family ',g, 'has no observations');
            writeln ('The first member of this family is',Families[g][1].ID);
         end;
         if mvert < vert[g] then mvert := vert[g];
 	 end; {g}
       writeln (Topend,' Over all families the largest # of observations is ');
       writeln (Topend, mvert:5,'  ( = pos )');
       end;

procedure Cleanup (var charnum: integer; var ntrnc: integer;
		   var nfxfact: integer);

   {reads and writes the parameters governing the run}

   var Analtype: integer;
      nvc, stot, totvar, i, index, feas, sv: integer;
   begin
      readln (sibships, Analtype, charnum, nfxfact, feas, sv);
      writeln (Analtype, ' Is the analysis type  ');
      writeln ('Number of traits is ', charnum:4);
      if charnum > r then begin
        writeln ('The constant "r" at the top of fend.p must be greater than',charnum);
        halt;
      end;
      writeln ('Number of fixed factors is  ',nfxfact);
      nvc := (charnum * (charnum+1)) div 2;
      writeln (Topend,'nvarcov = ',nvc);
      totvar := 6 * nvc;
      stot := 3 * nvc;
      writeln (Topend,'Total number of (co)variances ("maxnparm") ', totvar:4, ' for nf6.p');
      writeln (Topend,'Total number of (co)variances ("maxnparm") ', stot:4, ' for nf3.p');
   if sv = 1 then begin
     writeln ('This program will not accept starting values! Please run it without them!');
     halt;
   end;
      read (sibships, ntrnc);
      writeln ('Number of constrained components is ', ntrnc:4);
   if feas = 1 then writeln ('Automatic feasability constraining is invoked');
      for i := 1 to ntrnc do begin
         read (sibships, index);
         end;
      readln (sibships);
      end;

begin {program fend}
{unix initialization}
  reset(sibships,'sibships');
  rewrite (Topend,'Topend');
{Vax initialization}
  {open ( sibships, 'sibships', history := readonly );
  reset( sibships );
  open ( Topend, 'Topend', history := new );
  rewrite ( Topend );} 
   Cleanup (nchar, ntrunc, nfxfact);
   Getphtypes (PresentData, M, nchar, Zmatrix, slevels, nfxlevels);
   FindGroupsN (PresentData, M);
   famnum:= 0;
   for I := 1 to M do  begin
      if PresentData[I].Famid=0
      then begin
	 Check (I, PresentData, newfam);
	 if (newfam > 0)
	 then Visit (PresentData[I], newfam)
	 else begin
	    famnum:= famnum+1;
            if famnum > f then begin
              writeln ('The program is finding more families than are specified by f');
              writeln ('Raise this number!');
              halt;
            end;
	    Visit (PresentData[I], famnum);
	    end;
	 end;
      end;
   Collecthem(PresentData,Families, FamZ, famsize);
   Designit (FamZ, vert);
    end {program fend}.


