program nf3 (input, output);

{1-4-95}

const r=2; {r=the max. number of traits}
      nvarcov = 3; {the number of (co)variances of a given type; r*(r+1)/2}
      maxnparm=9; {the max. number of params}  {incl., Mat, Pat, k}
      emaxnparm=15; {the max. number of params incl lagrange multipliers}
      f=20;  {the max number of families}
      sibs=13; {max # of individuals in a family, including unmeasured}
      rhsibs=9;
      rfsibs=3; {max # of recip full sibs in a family}
      pos=18; {largest number of observations in a family (=< r*sibs)}
      nmax=260; {maximum total # of individuals in the dataset, including
                 those missing data}
      missing=-98; {Value in the dataset indicating missing phenotypic data}
      epsilon = 0.001;  {Convergence criterion}
      maxround=20;
      nf = 1;  {the max. number of fixed effects}
      p = 2;  {the maximum number of levels of fixed effects=r~nlevels}
      ceo = 1; {common environment option..4 for c.e, 1 for dominance}
      nconstr = 6; {maximum number of constraint equations to keep track of}

{The following commands must be issued prior to a run on a VAX:
    $ define sibships sibships
    $ define analysis analysis }

 type list = array[1..nf] of integer;
      Observation=record
                   ID:integer;
                   Father: integer;
                   Mother: integer;
                   NPS, NMS, FO, Famid: integer;
		   FixedVals: list;
                 end;  {Observation}
     Dataset=array[1..nmax] of Observation;
     slevelsbool = array[1..p] of boolean;
     Famset=array[1..sibs] of integer;
     Famarray=array[1..f] of Famset;
     Paramvar=array[1..r,1..r] of real;
     Parammean=array[1..p] of real;
     Parmvec=array[1..maxnparm] of real;
     eParmvec=array[1..emaxnparm] of real;
     Parmbool=array[1..maxnparm] of boolean;
     info = array [1..maxnparm,1..maxnparm] of real;
     einfo = array [1..emaxnparm,1..emaxnparm] of real;
     Vector=array[1..pos] of real;
     FamVector = array[1..f] of Vector;
     Covrow = array[1..pos] of real;
     ICovrow = array[1..pos] of integer;
     Covmatrix =  array[1..pos] of Covrow;
     Covarray = array[1..f] of Covmatrix;
     Desmatrix = array [1..pos,1..p] of integer;
     Desarray = array [1..f] of Desmatrix;
     Measures = array[1..nmax,1..r] of real;
     Famphens = array[1..pos,1..p] of real;
     Size=array[1..f] of integer;
     Traitsquare = array[1..p,1..p] of real;
     items = array[1..nf,1..p] of integer;
     amatrix = array[1..rhsibs] of Covrow;
     dmatrix = array[1..rfsibs] of Covrow;
     ematrix = array[1..1] of ICovrow;
     Desset = array[1..maxnparm] of Famphens;
     derivsa = array[1..nvarcov] of amatrix;
     derivsd = array[1..nvarcov] of dmatrix;
     derivse = array[1..nvarcov] of ematrix;
     Traitset = array[1..maxnparm] of Traitsquare;
     countrow = array[1..pos] of integer;
     countset = array[1..nvarcov] of countrow;
     lagvec = array[1..nconstr] of real;
     triplet = array[1..3] of real; {three component program}
     itriplet = array[1..3] of integer; {three component program}
     active = array[1..nconstr] of integer;

var  PresentData: Dataset;
     Design : Desarray;
     CU : Desset;
     Ldet :real;
     lln: lagvec;
     aset: active;
     cfactors: itriplet;
     LogLike, OldLogLike:real;
     XVY,WtdVals, Means: Parammean;
     AddCov, DomCov, EnvCov:Paramvar;
     D, SumD, Parms:Parmvec;
     eD : eParmvec;
     Zeroed : Parmbool;
     better, alldone, llpos, restart: boolean;
     Done, REML, ok, Maxed, Trunked: boolean;
     bfl, feasible : boolean;
     flagvec: slevelsbool;
     sibships: text;
     Analysis: text;
     nchar, ntrunc, slevels, nfxfact :integer;
     newfam, I, Iter, ncut, tncut: integer;
     Fm: Famarray;
     AB, VInvX: Famphens;
     Py: FamVector;
     M, famnum, vartypes : integer; {tot #, fam#, #types of comps estimable}
     Zmatrix:Measures;
     Q: Covarray;
     Vec, DiffVec, MeanVec:  Vector;
     famsize, vert: Size;
     Empty, cvec  : info;
     sBcov, XVXInv, XVX, Rfix : Traitsquare;
     UpCU, SumUpCU :  Traitset;   
     B, Inf, C, Big, RBig : info;
     eB, eC : einfo;
     nfxlevels: list; {contains the true number of levels for each fixed factor}
     levels: items; {Contains the values of the levels as in the data}
     DataVec: FamVector;


procedure Getphtypes(var Data:Dataset; var M: integer; var nchar:integer;
                     var Zmatrix: Measures; var slevels: integer;
		     var nfxlevels: list);

          {read the data from the input file. Each line of data is a record
          for an individual in the pedigree, containing, in order, an  ID
          number, the sire's ID, the dam's ID (the values of relatives 
          not present in the pedigree are assumed to be set at 0), 
          followed by phenotypic values for an arbitrary
          number of traits in a consistent order.  (The value of a
          trait that is missing for a given individual is assumed to be -99.
          Both parents of individuals for which phenotypic data is available
          must be included in the pedigree, regardless of whether
          phenotypic information is available for them.) In case the
          IDs of the individuals are not in order, they are put in order}

   var  TempID, TempFather, TempMother: integer;
        Pheno: real;
        I, J, K, L, which, count, obs, nobs:integer;
	already, mfl: boolean;

   begin
      obs := 0;
      nobs := 0;
      slevels := 0;
      for K := 1 to nfxfact do
         nfxlevels[K] := 0;
      M := 0;
      read (sibships,TempID);
      while not (TempID= 0) do begin
         M :=M+1;
         if M > nmax then begin
          writeln ('There are more data records than "nmax"');
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
               FixedVals[K] := which;
            end; 
          end; {with}
         mfl := false;
         for J := 1 to nchar do begin
            read (sibships, Pheno);
            if Pheno > missing then begin
              obs := obs + 1;
              mfl := true;
            end
             else nobs := nobs + 1;
            Zmatrix[M,J]:=Pheno;
         end;
         if mfl then begin
          with Data[M] do begin
            for K := 1 to nfxfact do begin
               which := FixedVals[K];
               already := false;
               count := 0;
               for L := 1 to nfxlevels[K] do begin
                  count := count + 1;
                  if (which=levels[K,L])
                  then begin
                    already := true;
                    FixedVals[K] := count;
                  end;
                end; {for L}
               if not already
               then begin
                  nfxlevels[K]:= nfxlevels[K] + 1;
                  FixedVals[K]:= nfxlevels[K];
                  write (Analysis, which,'is fixed effect number',nfxlevels[K]);
                  writeln (Analysis, 'of factor ', K);
                  slevels := slevels + 1;
                  levels[K,nfxlevels[K]] := which;
                  end;
               end; {K}
            end; {with}
         end; {if this record has an observation}
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
   if (nfxfact < 1)
   then slevels := 1;
   if (nfxfact > 1)
   then slevels := slevels - (nfxfact - 1); 
   slevels := nchar * slevels;
    if slevels > p then begin
     writeln ('The value of p set at the top of the program is too low. It must be at least ');
     writeln (slevels:5);
     halt;
    end;
    writeln ('The program has read',obs:6,' observations on',nchar:3,' traits.');
    writeln ('There were ',nobs:6,' missing observations.');
 end; {Getphtypes}

procedure FindGroupsN (var Data:Dataset; var M: integer);

  {The relationships within the pedigree are documented.  This information is
   stored in the "observation" records for use in finding families}

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
           if I < M then begin
  	   J := I + 1;
	    matched1 := false;
	    repeat 
               if (Data[J].Father = Dad) or (Data[J].Mother = Dad)
	       then begin
	          Data[I].NPS := J;
	          matched1 := true;
	          end;
	       J := J + 1;
	    until matched1 or (J>M-1);
	    end;
	   end;
         if Mom > 0 
	 then begin
            if Data[Mom].FO = 0
            then Data[Mom].FO := Me;
            if I < M then begin
  	    J := I + 1;
	    matched2 := false;
            repeat 
               if (Data[J].Father = Mom) or (Data[J].Mother = Mom)
	       then begin
	          Data[I].NMS := J;
	          matched2 := true;
	          end;
	       J := J + 1;
	    until matched2 or (J>M-1);
            end;
           end;
         end;
      end; {FindGroupsN}

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
      if Dad > 0
      then y := Data[Dad].Famid;
      if (y=0)
      then begin
         Mom := Data[I].Mother;
         if Mom > 0
         then y := Data[Mom].Famid;
	 end;
      end;

{procedure PrintFams (var Data: Dataset; Zmatrix:Measures);

   var I, J: integer;
   begin
  writeln (Analysis, 'Loc ID   ID  Father Mother NPS  NMS  Famid       Observations  ');
      for I := 1 to M do begin
         with Data[I] do begin
            write (Analysis, I:5, ID:5, Father:7, Mother:7, NPS:5);
            write (Analysis, NMS:5, Famid:5);
            end;
            for J:= 1 to nchar do
	      write (Analysis, Zmatrix[I,J]:8:2);
              writeln(Analysis);
      end;
   end;} {PrintFams}

procedure Collecthem (var Data: Dataset; var Fm: Famarray; var famsize: Size);

        {Index arrays are built for the families}

   var I, K, L : integer;
   begin {Collecthem}
      for I := 1 to famnum do begin
         L:=1;
         for K := 1 to M do begin
            if Data[K].Famid=I
            then begin
             if L > sibs then begin
              writeln ('Family ',I:5,' has too many individuals. Set sibs higher!');
              halt;
             end;
               Fm[I][L]:=K;
               L := L+1;
               end;
            end;
         famsize[I] := L-1;
         end;
       end; {Collecthem}

procedure CoeffMatrices (var Data: Dataset; var Fm: Famarray; 
                         var coeff: triplet; I, L, K: integer);

          {Coefficients of the causal components of variance
          are established on the basis of the pedigree information.
          Corrected 11-29-93 to properly initialize and work with new family structure.}

   var valA, valD, valE: real;
       SameFather, SameMother, Parent, Progen, Opposite1, Opposite2: boolean;

   begin {CoeffMatrices}
      if L=K
      then begin
         valA := 1.0;
         valD := 1.0;
         valE := 1.0;
         end  {Sameind}
      else begin
         Parent := false;
         Progen := false;
         SameFather := false;
         SameMother := false;
         Opposite1 := false;
         Opposite2 := false;
         valA := 0;
         valD := 0;
         valE := 0;
         if (Data[Fm[I][K]].Father > 0)
         then begin
 	    SameFather:=(Data[Fm[I][K]].Father=Data[Fm[I][L]].Father);
 	    Opposite1 :=(Data[Fm[I][K]].Father=Data[Fm[I][L]].Mother);
 	    end;
         if (Data[Fm[I][K]].Mother > 0)
         then begin
 	    SameMother:=(Data[Fm[I][K]].Mother=Data[Fm[I][L]].Mother);
 	    Opposite2 :=(Data[Fm[I][K]].Mother=Data[Fm[I][L]].Father);
 	    end;
         if SameMother or SameFather or Opposite1 or Opposite2
         then begin
           valA := 0.25;
            if (SameMother and SameFather) or (Opposite1 and Opposite2)
            then begin
               valA:= 0.5;
               valD:=0.25 * ceo;
            end;
         end {SameFather or SameMother or... or...}
         else begin
            Parent := (Data[Fm[I][L]].Father=Fm[I][K]) or
                            (Data[Fm[I][L]].Mother=Fm[I][K]);
            Progen := (Data[Fm[I][K]].Father=Fm[I][L])
                            or (Data[Fm[I][K]].Mother=Fm[I][L]);
            if Parent or Progen
            then valA:=0.5;
            end; {else (not SameFather or SameMother)}
         end; {else (not Samind)}
      coeff[1]:=valA;
      coeff[2]:=valD;
      coeff[3]:=valE;
      end; {CoeffMatrices}

procedure Designit (var Data: Dataset; var Fm: Famarray; var Zmatrix: Measures; var vert:Size;
                    var Design:Desarray; var DataVec: FamVector);

       {Produces the arrays Design(vert x nchar) (design matrix for the fixed
       effects in each family) and DataVec(g*vert x 1) (The nonmissing
       observations in the family).}

    var I, J, K, L, g: integer;
        vertical, col, item: integer;
    begin
       for g := 1 to famnum do begin
          vertical:=0;
          for I := 1 to pos do begin
             for J := 1 to slevels do
               Design[g][I,J] := 0;
             end;
          for I:=1 to famsize[g] do begin
            for J:=1 to nchar do begin
               if not (Zmatrix[Fm[g][I],J]<missing)
                then begin
                  vertical:=vertical+1;
 		  DataVec[g][vertical]:=Zmatrix[Fm[g][I],J];
 		  Design[g][vertical,J] := 1;
 		  item := 0;
 		  for L := 1 to nfxfact do begin
 		     item := Data[Fm[g][I]].FixedVals[L]-1;
 		     col := nchar;
		     for K := 1 to (L-1) do
 		        col:= col + nchar*(nfxlevels[K]-1);
                     if item > 0
 		     then begin
		        col := col + (item-1)*nchar + J;
 		        Design[g][vertical,col] := 1;
			end;
 		     end; {L}
 		  end; {if}
 	       end; {J}
             end; {I}
 	 vert[g] := vertical;
 	 end; {g}
       end;

procedure ZeroEmpty (var Empty: info);
   var i,j: integer;
   begin
     for i := 1 to maxnparm do begin
        for j := 1 to maxnparm do
           Empty[i,j] := 0;
        end;
     end;

procedure EnterValues(var AddCov, DomCov, EnvCov:Paramvar);

         {values for the variance components are transferred
         into the matrices of variance and covariance components
         of the traits.}

   var I,J: integer;
       add, group, loc: integer;
   begin
      group := (nchar *(nchar+1)) div 2;
      add := 0;
      for I:=1 to nchar do begin
         for J:=I to nchar do begin
            add := add + 1;
            AddCov[I,J]:= Parms[add];
            AddCov[J,I] := AddCov[I,J];
            loc := group + add;
            EnvCov[I,J] := Parms[loc];;
            EnvCov[J,I] := EnvCov[I,J];
            loc := loc + group;
            DomCov[I,J]:= Parms[loc];
            DomCov[J,I]:=DomCov[I,J];
            end; {J loop}
         end;
      end;   {EnterValues}

procedure MakeCovArray (var EstCovArray:Covarray);

 {The V matrix is assembled.}

   var G, I, J, K, L, skippedi, skippedj: integer;
       X, Y :integer;
       coeff: triplet;
   begin
      for G:= 1 to famnum do begin
      skippedi:=0;
         for I:= 1 to famsize[G] do begin
            for K:= 1 to nchar do begin
               if (Zmatrix[Fm[G][I],K]<missing)
               then skippedi := skippedi + 1
               else begin
                  X:= (I-1) * nchar + K - skippedi;
                  skippedj:=0;
                  for J:= 1 to famsize[G] do begin
                     for L:= 1 to nchar do begin
                        if (Zmatrix[Fm[G][J],L]<missing)
                        then skippedj := skippedj + 1
                        else begin
                           Y:= (J-1) * nchar + L - skippedj;
                           CoeffMatrices(PresentData,Fm,coeff,G,I,J);
                           EstCovArray[G][X][Y]:=coeff[1] * AddCov[K,L] +
                                           coeff[2] * DomCov[K,L] +
                                           coeff[3] * EnvCov[K,L];
                           end; {else}
                        end; {L loop}
                     end; {J loop}
                  end; {else}
               end; {K loop}
            end; {I loop}
         end; {G loop}
end; {MakeCovMatrix}

procedure ComputeLogLikelihood (var LogLike: real;
                                 var Q: Covarray; var Means: Parammean;
                                 var XVXInv: Traitsquare;  var Py : FamVector;
                                 var vert: Size;  var DataVec: FamVector;
				 var Design: Desarray; var ok:boolean);
   var g,I,J: integer;
       Matprod, SumLdet, XVXdet: real;
       SumS: real;

   procedure GetWtdVals (var WtdVals: Parammean; var VInvX: Famphens;
                         upper: integer; var DataVec: Vector; 
                         var Des: Desmatrix);
      {WtdVals: X'VInv y}

      var i, j, k :integer;
          tally : real;
      begin
         for i := 1 to upper do begin
            for j:= 1 to slevels do begin
               tally := 0;
               for k:= 1 to upper do
                  tally := Q[g][i][k] * Des[k,j] + tally;
               VInvX[i,j] := tally;
               end;
            end;
         for i := 1 to slevels do begin
            WtdVals[i] := 0;
            for j := 1 to upper do
               WtdVals[i] := VInvX[j,i] * DataVec[j] + WtdVals[i];
            end;
         end;

   procedure Vechs (var MeanVec: Vector; Means: Parammean;
                    var Des: Desmatrix; upper: integer);
      {Vechs produces MeanVec, a vector of the means corresponding to the
      measures in DataVec.}
      var i, j : integer;
      begin
         for i := 1 to upper do begin
	    MeanVec[i] := 0.0;
            for j := 1 to slevels do begin
               if Des[i,j] = 1
               then MeanVec[i] := Means[j] + MeanVec[i];
               end;
            end;
         end;

procedure Standardize (DataVec: Vector; MeanVec: Vector; upper: integer;
                          var DiffVec: Vector);
      {DiffVec is the deviations of the measures from their means.}
      var I : integer;
      begin
         for I:=1 to upper do begin
            DiffVec[I]:=DataVec[I]-MeanVec[I];
            end;
         end;

procedure VMatrixInversion (var A:Covmatrix; var Ldet: real; n: integer;
                           var ok: boolean);
   {Invert by triangularization. Return the inverse.}
   procedure Rootit (var A: Covmatrix; var Ldet: real; var ok: boolean);
     {The square root.}
      var i, j, k: integer;
          sum: real;

   procedure printparms;

    {print parameters in case of non-pos-def V matrix}

   var i, j, l: integer;

   begin
    writeln ('The current estimates: ');
    writeln ( '    Additive');
    writeln ('              ');
    l := 1;
    for i := 1 to nchar do begin
       for j := i to nchar do begin
          write (Parms[l]:14:6);
          l := l+1;
          end;
       writeln;
       for j := 1 to i do
       write ('              ');
       end;
    writeln;
    writeln ( '   Environmental');
    writeln ('              ');
    for i := 1 to nchar do begin
       for j := i to nchar do begin
          write (Parms[l]:14:6);
          l := l+1;
          end;
       writeln;
       for j := 1 to i do
       write ('              ');
       end;
    writeln;
    if ceo = 1 then
    writeln ( '   Dominance')
    else writeln ( '   Common Environment');
    writeln ('              ');
    for i := 1 to nchar do begin
       for j := i to nchar do begin
          write ( Parms[l]:14:6);
          l := l+1;
          end;
       writeln;
       for j := 1 to i do
       write ('              ');
       end;
    writeln;
    writeln ('It is suggested that a smaller model be tried in which');
    writeln ('components which are negative here are constrained to zero.');
   end; {printparms}

      begin {rootit}
        if (A[1][1] < 0)
        then begin
	   ok := false;
           writeln ('The variance matrix is not pos. def.');
           printparms;
           halt;
	   end
        else begin
           A[1][1] := sqrt(A[1][1]);
           for i := 2 to n do
              A[i][1] := A[i][1]/A[1][1];
           for i := 2 to n do begin
              sum := 0.0;
              for j := 1 to (i-1) do
                 sum := sum +sqr(A[i][j]);
              if (A[i][i] < sum)
              then begin 
                writeln ('The Variance Matrix is not positive definite');
                printparms;
                halt;
              end
              else begin
                 A[i][i] := sqrt(A[i][i]-sum);
                 if (i<n) then begin
                   for j := (i+1) to n do begin
                     sum := 0.0;
                     for k := 1 to (i-1) do
                       sum := sum + A[i][k] * A[j][k];
                       A[j][i] := (A[j][i]-sum)/ A[i][i];
                     end;
                   end;
                 end;
              end;
            end;
         Ldet := 0;
         for i := 1 to n do
            Ldet := Ldet + ln(A[i][i]);
         Ldet := 2*Ldet;
         end;

   procedure Invertit (var A: Covmatrix);
      {The inverse of the root, followed by L'*L.}
      var i, j, k : integer;
          one : real;
          sum : real;
      begin
         one := 1.0;
         for i := 1 to n do begin
            A[i][i] := one/A[i][i];
            for j := (i+1) to n do begin
               sum := 0.0;
               for k := i to (j-1) do
                  sum := sum + A[j][k]*A[k][i];
               A[j][i] := -sum/A[j][j];
               end;
            end;
         for i := 1 to n do begin
            for j := i to n do begin
               sum := 0.0;
               for k := j to n do
                  sum := sum + A[k][i] * A[k][j];
               A[i][j] := sum;
               end;
            end;
            for i := 1 to n do begin
             for j := i to n do begin
             A[j][i] := A[i][j];
             end;
            end;
         end;

      begin {VMatrixInversion}
	 ok := true;
         Rootit(A, Ldet, ok);
         Invertit(A);
      end;

procedure sMatrixInversion (var A:Traitsquare; var Ldet: real; n: integer;
                           var ok: boolean);
   {Invert by triangularization. Return the inverse.}
   procedure sRootit (var A: Traitsquare; var Ldet: real; var ok: boolean);
     {The square root.}
      var i, j, k: integer;
          sum: real;
      begin
        if (A[1][1] < 0)
        then begin
	   ok := false;
           writeln (Analysis,'The XVX matrix is not pos. def.');
	   end
        else begin
           A[1][1] := sqrt(A[1][1]);
           for i := 2 to n do
              A[i][1] := A[i][1]/A[1][1];
           for i := 2 to n do begin
              sum := 0.0;
              for j := 1 to (i-1) do
                 sum := sum +sqr(A[i][j]);
              if (A[i][i] < sum)
              then ok := false
              else begin
                 A[i][i] := sqrt(A[i][i]-sum);
                 if (i<n) then begin
                   for j := (i+1) to n do begin
                     sum := 0.0;
                     for k := 1 to (i-1) do
                       sum := sum + A[i][k] * A[j][k];
                       A[j][i] := (A[j][i]-sum)/ A[i][i];
                     end;
                   end;
                 end;
              end;
            end;
         Ldet := 0;
         for i := 1 to n do
            Ldet := Ldet + ln(A[i][i]);
         Ldet := 2*Ldet;
         end;

   procedure sInvertit (var A: Traitsquare);
      {The inverse of the root, followed by L'*L.}
      var i, j, k : integer;
          one : real;
          sum : real;
      begin
         one := 1.0;
	 for i := 1 to n do
            sBcov[i] := A[i];
         for i := 1 to n do begin
            sBcov[i][i] := one/A[i][i];
            for j := (i+1) to n do begin
               sum := 0.0;
               for k := i to (j-1) do
                  sum := sum + A[j][k]*sBcov[k][i];
               sBcov[j][i] := -sum/A[j][j];
               end;
            end;
         for i := 1 to n do begin
            for j := i to n do begin
               sum := 0.0;
               for k := j to n do
                  sum := sum + sBcov[k][i] * sBcov[k][j];
               A[i][j] := sum;
               A[j][i] := sum;
               end;
            end;
         end;
      begin {sMatrixInversion}
	 ok := true;
         sRootit(A, Ldet, ok);
         sInvertit(A);
      end;

   procedure FormPy (var Q: Covmatrix; var Py:Vector; upper: integer);
          {Py is VInv * DiffVec.}
      var I, J: integer;
          tally: real;
      begin
         Vec := DiffVec;
         for I := 1 to upper do begin
            tally := 0;
            for J := 1 to upper do
               tally := Q[I][J]*Vec[J] + tally;
            Py[I] := tally;
            end;
         end;

   procedure Correction (var Rfix: Traitsquare; Des:Desmatrix);
      {Rfix is X' VInv X for a single family.}
      var j, k, l : integer;
      begin
         for j := 1 to slevels do begin
            for l:= 1 to vert[g] do begin
               VInvX[l,j] :=0;
               for k := 1 to vert[g]
               do VInvX[l,j] := Des[k,j]*Q[g][k][l] + VInvX[l,j];
               end; {l}
            end; {j}
         for j := 1 to slevels do begin
            for l := 1 to slevels do begin
               Rfix[j,l] :=0;
               for k := 1 to vert[g]
                 do Rfix[j,l] := VInvX[k,j] * Des[k,l] + Rfix[j,l];
               end; {l}
            end; {j}
      end; {Correction}

   procedure InvertXVX (var XVX: Traitsquare; var XVXInv: Traitsquare;
                        var bfl: boolean; var flagvec: slevelsbool;
                        var XVXdet: real; slevels: integer);

   {This procedure truncates the XVX matrix in case it's degenerate..
    a situation arising from the absence of observed individuals in
    some fixed factor at some level}

   var i, j, s, t: integer;
   var flag: boolean;
   
     begin
      if Iter = 1 
      then begin
      bfl := true;
      for i := 1 to slevels do begin
       flag := false;
       flagvec[i] := true;
       for j := 1 to slevels do
       if (abs(XVX[i,j]) > 1.0E-08 ) then flag := true;
       if flag = false
        then begin
        flagvec[i] := false;
        bfl := false;
        end;
       end; {i}
       end; {iter = 1} 
      if bfl = false 
      then begin
      s := 0;
      for i := 1 to slevels do begin
         t := 0;
         if flagvec[i]
         then begin
            s := s + 1;
            for j := 1 to slevels do begin
               if flagvec[j]
               then begin
                  t := t + 1;
                  XVX[s,t] := XVX[i,j];
                  end;
               end;
            end;
         end;
      end
   else s:= slevels;
   sMatrixInversion(XVX,XVXdet,s,ok);
      s := 0;
      for i := 1 to slevels do begin
         t := 0;
         if flagvec[i]
         then begin
            s := s + 1;
            for j := 1 to slevels do begin
               if flagvec[j]
               then begin
                  t := t + 1;
                  XVXInv[i,j] := XVX[s,t];
                  end
               else XVXInv[i,j] := 0.0;
               end;
            end
         else begin
            for j := 1 to slevels do
               XVXInv[i,j] := 0.0;
            end;
         end;
    end;  {procedure}

   procedure EstimateMeans (var Means: Parammean);
      {The means are estimated as (X'VInvX)Inv* X'VInvY.}
      var i, j : integer;
          tally : real;
      begin
         for i := 1 to slevels do begin
            tally := 0;
            for j:= 1 to slevels do
                  tally := XVXInv[i,j] * XVY[j] + tally;
               Means[i] := tally;
            end;
          end;
   begin {ComputeLogLikelihood}
      Matprod:=0;
      SumS:=0;
      SumLdet :=0;
      for I := 1 to slevels do begin
         for J := 1 to slevels do begin
            XVX[I,J] := 0;
            XVXInv[I,J] := 0;
            end;
         XVY[I] := 0;
         end;
      for g:=1 to famnum do begin
         VMatrixInversion (Q[g],Ldet, vert[g], ok);
         SumLdet := Ldet + SumLdet;
         Correction (Rfix, Design[g]);
         for I:= 1 to slevels do begin
            for J := 1 to slevels do
               XVX[I,J] := Rfix[I,J] + XVX[I,J];
            end;
         GetWtdVals (WtdVals, VInvX, vert[g], DataVec[g],Design[g]);
         for I := 1 to slevels do
            XVY[I] := WtdVals[I] + XVY[I];
      end; {g}
      InvertXVX (XVX,XVXInv,bfl,flagvec,XVXdet,slevels);
      writeln ('done 2nd inversion');
      SumS := XVXdet;
      EstimateMeans (Means);
      for g := 1 to famnum do begin
         Vechs (MeanVec, Means, Design[g], vert[g]);
         Standardize (DataVec[g], MeanVec, vert[g], DiffVec);
         FormPy (Q[g], Py[g], vert[g]);
         for I:=1 to vert[g] do
	     Matprod:=DiffVec[I]*Py[g][I]+Matprod;
         end; {g}
      if REML
        then LogLike:=-(Matprod+SumLdet+SumS)/2
        else LogLike := -(Matprod + SumLdet)/2;
     {writeln ('Matprod  SumLdet  ', Matprod:16:9, SumLdet:16:9);}
     writeln (Analysis,'LogLike ', LogLike:15:4);
     writeln ('LogLike ', LogLike:15:4);
   end;{Compute LogLikelihood}

procedure MatrixInversion (var A:info ; dim: integer);
var i, j, k, lower, upper : integer;
      temp: real;
begin {Gauss-Jordan reduction -- invert
       matrix in place, overwriting previous
       contents of A.}
   lower := 1;
    upper := dim;
    for i := lower to upper do begin
      if A[i,i] = 0
      then writeln ('the info matrix is singular');
      temp := 1.0 / A[i, i];
      A[i, i] := 1.0;
      for j := lower to upper do
         A[i, j] := A[i, j] * temp;
      for j := lower to upper do
         if j <> i
         then begin
            temp := A[j, i];
            A[j,i] := 0.0;
            for k := lower to upper do
               A[j, k] := A[j, k] - temp * A[i, k];
            end;
      end;
end; {invert}

procedure CalcNewEsts (var Parms: Parmvec; var lln: lagvec; 
                       var aset: active; var Inf, B: info;
                       var ncut: integer);

   {New estimates are calculated using Fisher's scoring method. (See K.
   Meyer, 1983. J. Dairy Sci. 66: 1988-1997.  The inverse of the information
   matrix (B) and the first derivatives of the likelihood function with
   respect to each parameter (D) are obtained.  The new vector of estimates
   is Binv * y'P * Py. The info matrix B is tr PdvdtPdvdt or -1/2 of expected
   Hessian}

 var length, nvarparms, totvar : integer;
     fcount, fc, i, j, k, s, t: integer;
     tally : real;
     tdva, tdvd, tdve: countset;
     DVA : derivsa;
     DVD : derivsd;
     DVE : derivse;

procedure DVprods (var DVA:derivsa; var DVD:derivsd; var DVE:derivse;
			      var tdva, tdvd, tdve: countset; 
			      length:integer; var Psub: Vector;
			      var D:Parmvec; var CU:Desset; var AB: Famphens);

      type shortarray=array[1..p] of real;

      var g, i, s, j, nvc : integer;
	  index: integer;
	  tally, fact:real;
          t:shortarray;

      begin
         nvc := (nchar * (nchar+1)) div 2;
	 for g := 1 to totvar do
	    D[g] := 0.0;
         for g := 1 to nvc do begin
     if ((not Trunked) or (not Zeroed[g])) then begin
	    for i := 1 to length do begin
	       tally := 0.0;
	       for s := 1 to slevels do
                  t[s] := 0;
               for j := 1 to tdva[g][i] do begin
                  index := trunc(DVA[g][j][i]);
                  fact := DVA[g][j][i]-index;
                  fact := fact*2.0;
                  tally := tally + Psub[index]*fact;
                  if REML
                  then begin
                    for s := 1 to slevels do
                       t[s] := t[s] + AB[index,s]*fact;
                    end;
                 end;
             D[g] := D[g] + Psub[i] * tally;
	     if REML
	     then begin
		for s := 1 to slevels do
   	           CU[g][i][s] := t[s];
                end;
	     end;
     end; {if not Trunked}
     if ((not Trunked) or (not Zeroed[g+nvc])) then begin
	    for i := 1 to length do begin
	       tally := 0.0;
	       for s := 1 to slevels do
                  t[s] := 0;
               for j := 1 to tdve[g][i] do begin
		  index := DVE[g][j][i] ;
		  tally := tally + Psub[index];
		  if REML 
		  then begin
		    for s := 1 to slevels do
		       t[s] := t[s] + AB[index,s];
                    end;
                 end;
             D[g+nvc] := D[g+nvc] + Psub[i] * tally;
	     if REML
	     then begin
		for s := 1 to slevels do
   	           CU[g+nvc][i][s] := t[s];
                end;
	     end;
     end; {if not Trunked}
     if ((not Trunked) or (not Zeroed[g+2*nvc])) then begin
	    for i := 1 to length do begin
	       tally := 0.0;
	       for s := 1 to slevels do
                  t[s] := 0;
               for j := 1 to tdvd[g][i] do begin
                  index := trunc(DVD[g][j][i]);
                  fact := DVD[g][j][i]-index;
                  fact := fact*2.0;
                  tally := tally + Psub[index]*fact;
                  if REML
                  then begin
                    for s := 1 to slevels do
                       t[s] := t[s] + AB[index,s]*fact;
                    end;
                 end;
             D[g+2*nvc] := D[g+2*nvc] + Psub[i] * tally;
	     if REML
	     then begin
		for s := 1 to slevels do
   	           CU[g+2*nvc][i][s] := t[s];
                end;
	     end;
     end; {if not Trunked}
	 end; {g}
      end;{DVprods}

   procedure MakeA (var Des: Desmatrix; var VInv: Covmatrix;
		    var VInvX: Famphens);
      {A is VInvX.}
      var w,t,s : integer;
          tally : real;
      begin
         for w := 1 to length do begin
            for t := 1 to slevels do begin
               tally := 0;
               for s := 1 to length do
                  tally := VInv[w][s]*Des[s,t] + tally;
               VInvX[w,t] := tally;
               end;
            end;
         end;

   
procedure Root (var A: Traitsquare; n: integer);
     {The square root.}
      var i, j, k: integer;
          sum: real;
      begin
         A[1,1] := sqrt(A[1,1]);
         for i := 2 to n do
            A[i,1] := A[i,1]/A[1,1];
       for i := 2 to n do begin
            sum := 0.0;
            for j := 1 to (i-1) do
               sum := sum +sqr(A[i,j]);
            A[i,i] := sqrt(A[i,i]-sum);
            if (i<n) then begin
               for j := (i+1) to n do begin
                  sum := 0.0;
                  for k := 1 to (i-1) do
                     sum := sum + A[i,k] * A[j,k];
                 A[j,i] := (A[j,i]-sum)/ A[i,i];
                 end;
               end;
            end;
         end;

procedure MakeAB (var AB, VInvX: Famphens);
   var w, t, s: integer;
       tally: real;
   begin
      for w := 1 to vert[fcount] do begin
         for t:= 1 to slevels do begin
            tally := 0;
            for s := t to slevels do
               tally := VInvX[w,s]*XVXInv[s,t] + tally;
            AB[w,t] := tally;
            end;
         end;
      end;

   
procedure MakeFirsts (var DVA:derivsa; var DVD:derivsd; var DVE:derivse;
                      var tdva, tdvd, tdve: countset; var G: integer);

 {Compute family G's derivative matrices.  The coefficients for the A and D
  matrices are stored by halving in case manipulation of these coefficients is
  desired}

   var I, J, K, L, skippedi, skippedj: integer;
       X, Y, s, t, u:integer;
       coeff: triplet;

   begin {initialize}
   for I := 1 to nvarcov do begin
    for J := 1 to pos do begin
      tdva[I][J] := 0;
      tdvd[I][J] := 0;
      tdve[I][J] := 0;
    end;
   end;
      skippedi:=0;
         for I:= 1 to famsize[G] do begin
            for K:= 1 to nchar do begin
               if (Zmatrix[Fm[G][I],K]<missing)
               then skippedi := skippedi + 1
               else begin
                  X:= (I-1) * nchar + K - skippedi;
                  skippedj:=0;
                  for J:= 1 to famsize[G] do begin
                     for L:= 1 to nchar do begin
                        if (Zmatrix[Fm[G][J],L]<missing)
                        then skippedj := skippedj + 1
                        else begin
                           Y:= (J-1) * nchar + L - skippedj;
                           CoeffMatrices(PresentData,Fm,coeff,G,I,J);
                        u := 0;
                        for s := 1 to nchar do begin
                           for t := s to nchar do begin
                              u := u + 1;
                              if (K=s) and (L=t) or ((K=t) and (L=s))
                              then begin
				 if (coeff[1]>0)
				 then begin
				    tdva[u][X] := tdva[u][X] + 1;
                                    DVA[u][tdva[u][X]][X]:=coeff[1]/2.0 + Y;
				    end;
				 if (coeff[2]>0)
				 then begin
				    tdvd[u][X] := tdvd[u][X] + 1;
                                    DVD[u][tdvd[u][X]][X]:=coeff[2]/2 + Y;
				    end;
				 if (coeff[3]>0)
				 then begin
				    tdve[u][X] := tdve[u][X] + 1;
                                    DVE[u][tdve[u][X]][X]:=Y;
				    end;
                                 end {if}
                              end;{t loop}
                             end; {s loop}
                           end; {else}
                        end; {L loop}
                     end; {J loop}
                  end; {else}
               end; {K loop}
            end; {I loop}
end; {MakeFirsts}

   procedure ComputeBig (var Q: Covmatrix; var B: info; length, totvar:integer);
      {The information matrix for a given family is generated.  Each element
      is the trace of (VInv dVdI VInv dVdJ).  These are summed over families
      in the main procedure to give the info matrix for the whole dataset.}
      type linemat=array[1..maxnparm,1..pos] of real;
      var g, h, i, j, k, l, m, index, nvc: integer;
        tally, fact: real;
	  QGI, QHI: linemat;
      begin
        nvc := (nchar * (nchar + 1)) div 2;
	for i := 1 to length do begin
	   for j := 1 to totvar do begin
	      for k := 1 to length do begin
                 QHI[j,k] := 0.0;
                 QGI[j,k] := 0.0;
		 end;
              end;
	   for j := 1 to nvc do begin
	      for k := i to length do begin
		 tally := 0.0;
        if ((not Trunked) or (not Zeroed[j])) then begin
		 for l := 1 to tdva[j][k] do begin
                    index := trunc(DVA[j][l][k]);
		    fact := DVA[j][l][k] - index;
                    fact := fact * 2;
		    tally := tally + Q[i][index]*fact;
		    end; {l}
                 QGI[j,k] := tally;
        end; {if not Trunked}
        if ((not Trunked) or (not Zeroed[j+2*nvc])) then begin
		 tally := 0.0;
		 for l := 1 to tdvd[j][k] do begin
		    index := trunc(DVD[j][l][k]);
                    fact := DVD[j][l][k] - index;
                    fact := fact * 2;
		    tally := tally + Q[i][index] * fact;
		    end; {l}
                 QGI[j+2*nvc,k] := tally;
        end; {if not Trunked}
        if ((not Trunked) or (not Zeroed[j+nvc])) then begin
		 for l := 1 to tdve[j][k] do begin
                    index := DVE[j][l][k];
                    QGI[j+nvc,k] := Q[i][index];
                    end; {l}
        end; {if not Trunked}
        end; {k}
        if ((not Trunked) or (not Zeroed[j])) then begin
		 for m := 1 to tdva[j][i] do begin
		    index := trunc(DVA[j][m][i]);
		    fact := DVA[j][m][i] - index;
                    fact := fact * 2;
		    for k := i to length do
		       QHI[j,k] := QHI[j,k] + Q[k][index]*fact;
		    end; {m}
        end; {if not Trunked}
        if ((not Trunked) or (not Zeroed[j+2*nvc])) then begin
		 for m := 1 to tdvd[j][i] do begin
		    index := trunc(DVD[j][m][i]);
		    fact := DVD[j][m][i] - index;
                    fact := fact * 2;
		    for k := i to length do
		    QHI[j+2*nvc,k] := QHI[j+2*nvc,k] + Q[k][index]*fact;
		    end; {m}
        end; {if not Trunked}
        if ((not Trunked) or (not Zeroed[j+nvc])) then begin
		 for m := 1 to tdve[j][i] do begin
		    index := DVE[j][m][i];
		    for k := i to length do
		       QHI[j+nvc,k] := Q[k][index];
		    end; {m}
        end; {if not Trunked}
		 end;  {j}
              for g := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[g])) then begin
                 for h := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[h])) then begin
                    tally := QGI[g,i] * QHI[h,i]/2.0;
                    for l := i+1 to length do begin
                       tally := tally + QGI[g,l] * QHI[h,l];
                       end;
                    B[g,h] := B[g,h] + tally;
              end; {if no Trunked h}
                    end; {h}
              end; {if not Trunked g}
                 end; {g}
              end; {i}
          {even it up}
              for g := 1 to totvar do begin
                 for h := g to totvar do begin
                    B[g,h] := B[g,h] + B[h,g];
                    B[h,g] := B[g,h];
                 end; {h}
              end; {g}
           end; {ComputeBig}

procedure Moreprods (var UpCU: Traitset; var CU: Desset; var RBig: info;
                     var V: Covmatrix);
   var i, w, j, s, q, t, n : integer;
       tally : real;
   begin
      n := vert[fcount];
      for i := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[i])) then begin
         for t := 1 to slevels do begin
            for w := 1 to slevels do begin
               tally := 0;
               for j := 1 to n do
                  tally := AB[j,t]*CU[i][j,w] + tally;
               UpCU[i][t,w] := tally;
               end;
            end;
         for s := 1 to n do begin
            for q := 1 to slevels do begin
               tally := 0;
               for t := 1 to n do
                  tally := V[s][t]*CU[i][t,q]+tally;
               VInvX[s,q] := tally;
               end;
            end;
        for j := i to totvar do begin
        if ((not Trunked) or (not Zeroed[j])) then begin
           tally := 0;
           for s := 1 to slevels do begin
              for q := 1 to n do
                 tally := CU[j][q,s]*VInvX[q,s] + tally;
              end;
           RBig[i,j] := -2*tally;
           RBig[j,i] := -2*tally;
           {This RBig is the second term in the expression for the info matrix
            for REML: see Meyer, K. 1983. eq. 9, substituting in the expression
            for P and multiplying out gives 4 terms.  The first is just the
            same as the info matrix for ML, the middle two can be combined and
            rearranged to give -2*tr(u'dV/dTj*VInv*dV/DTi*u), where
            uu'=VInvX(X'*VInv*X)X'VInv.  This term is the quantity caluclated
            this procedure.  See ComputeRBig for the last term.}
        end; {if not Trunked j}
           end; {j}
        end; {if not Trunked i}
        end; {i}
      end; {Moreprods}

procedure ComputeRBig (var RBig: info; var SumUpCU:Traitset);
   {Compute the last term in the info matrix of REML.  It is
   tr(u'dV/dTiu)(u'dV/dTju), where u is defined in Dvprods.
   see Meyer in J. Dairy Sci).}
   var tally : real;
       i, j, p, q : integer;
   begin
      for i := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[i])) then begin
         for j := i to totvar do begin
        if ((not Trunked) or (not Zeroed[j])) then begin
            tally := 0;
            for q := 1 to slevels do begin
               for p := 1 to slevels do
                  tally := SumUpCU[i][q,p]*SumUpCU[j][p,q] + tally;
               end;
            RBig[i,j] := tally;
            RBig[j,i] := tally;
        end; {if not Trunked j}
            end; {j}
        end; {if not Trunked i}
         end; {i}
     end; {ComputeRBig}

procedure MatrixInversion (var A:info ; dim: integer);
var i, j, k, lower, upper : integer;
      temp: real;
begin {Gauss-Jordan reduction -- invert
       matrix in place, overwriting previous
       contents of A.}
   lower := 1;
    upper := dim;
    for i := lower to upper do begin
      if A[i,i] = 0
      then writeln ('the info matrix is singular');
      temp := 1.0 / A[i, i];
      A[i, i] := 1.0;
      for j := lower to upper do
         A[i, j] := A[i, j] * temp;
      for j := lower to upper do
         if j <> i
         then begin
            temp := A[j, i];
            A[j,i] := 0.0;
            for k := lower to upper do
               A[j, k] := A[j, k] - temp * A[i, k];
            end;
      end;
   end; {invert}

procedure eMatrixInversion (var A:einfo ; dim: integer);
var i, j, k, lower, upper : integer;
      temp: real;
begin {Gauss-Jordan reduction -- invert
       matrix in place, overwriting previous
       contents of A.}
   lower := 1;
    upper := dim;
    for i := lower to upper do begin
      if A[i,i] = 0
      then writeln ('the info matrix is singular');
      temp := 1.0 / A[i, i];
      A[i, i] := 1.0;
      for j := lower to upper do
         A[i, j] := A[i, j] * temp;
      for j := lower to upper do
         if j <> i
         then begin
            temp := A[j, i];
            A[j,i] := 0.0;
            for k := lower to upper do
               A[j, k] := A[j, k] - temp * A[i, k];
            end;
      end;
   end; {invert}

   procedure Newtheta (D: Parmvec; var Theta: Parmvec; upper: integer);
      {takes the product of BInv and D to give new parameter estimates}
      var i, j: integer;
      begin
         for i := 1 to upper do begin
            Theta[i] := 0;
            for j := 1 to upper do begin
               Theta[i] := B[i,j] * D[j] + Theta[i];
               end;
             end; {i}
          end;

   procedure eNewtheta (eD: eParmvec; var eB: einfo; 
                        var Theta: Parmvec; upper: integer; 
                        var ncut: integer; var lln: lagvec; var aset: active);
      {takes product of hessian and derivitive to get new parms and lln}
      var i, j: integer;
      var tally: real;
      begin
         for i := 1 to upper do begin
             tally := 0.0;
            for j := 1 to upper + ncut do
               tally := eB[i,j] * eD[j] + tally;
               Theta[i] := Theta[i] - tally;
            end;
         for i := 1 to ncut do begin
             tally := 0.0;
            for j := 1 to upper + ncut do 
              tally := tally + eB [upper+i, j] * eD [j];
              lln[aset[i]] := lln[aset[i]]- tally;
           writeln ('Multiplier',aset[i]:3,lln[aset[i]]:8:4);
           writeln (Analysis,'Multiplier',aset[i]:3,lln[aset[i]]:8:4);
          end; {i}
          end;

 begin {CalcNewEsts}
    B := Empty;
    RBig := Empty;
    nvarparms := (nchar * (nchar +1)) div 2;
    totvar := vartypes * nvarparms;
    for i := 1 to totvar do begin
       SumD[i] := 0;
       for j := 1 to slevels do begin
          for k := 1 to slevels do
             SumUpCU[i][j,k] := 0;
          end;
       end;
     if not restart then begin
      XVX := XVXInv;
      if bfl = false 
      then begin
      s := 0;
      for i := 1 to slevels do begin
         t := 0;
         if flagvec[i]
         then begin
            s := s + 1;
            for j := 1 to slevels do begin
               if flagvec[j]
               then begin
                  t := t + 1;
                  XVX[s,t] := XVX[i,j];
                  end;
               end;
            end;
         end;
      end
   else s:= slevels;
    Root (XVX, s); 
      s := 0;
      for i := 1 to slevels do begin
         t := 0;
         if flagvec[i]
         then begin
            s := s + 1;
            for j := 1 to slevels do begin
               if flagvec[j]
               then begin
                  t := t + 1;
                  XVXInv[i,j] := XVX[s,t];
                  end
               else XVXInv[i,j] := 0.0;
               end;
            end
         else begin
            for j := 1 to slevels do
               XVXInv[i,j] := 0.0;
            end;
         end;
    end; {if not restart}
    for fcount := 1 to famnum do begin
       fc := fcount;
       length := vert[fcount];
       if REML
       then begin
  	  MakeA (Design[fcount],Q[fcount],VInvX);
          MakeAB (AB,VInvX);
          end;
       MakeFirsts (DVA,DVD,DVE,tdva,tdvd,tdve,fc);
       DVprods (DVA,DVD,DVE,tdva,tdvd,tdve,length,Py[fcount],D,CU,AB);
       Big := Empty;
       ComputeBig (Q[fcount],Big, length, totvar);
       for i := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[i])) then begin
          SumD[i] := D[i] + SumD[i];
          for j := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[j])) then begin
             B[i,j] := Big[i,j] + B[i,j];
             end; {if not Trunked j}
            end;{j}
            end; {if not Trunked i}
          end; {i}
       if REML
       then begin
          Moreprods (UpCU, CU, RBig, Q[fcount]);
          for i := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[i])) then begin
             for j := 1 to slevels do begin
                for k := 1 to slevels do
                   SumUpCU[i][j,k] := SumUpCU[i][j,k] + UpCU[i][j,k];
                end;
             for j := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[j])) then begin
                B[i,j] := B[i,j] + RBig[i,j];
             end; {if not Trunked j}
             end; {j}
             end; {j}
          end; {if not Trunked i}
          end; {i}
       end; {fcount}
      if REML
      then begin
         ComputeRBig (RBig, SumUpCU);
	 writeln ('done computeRbig');
         for i := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[i])) then begin
             for j := 1 to totvar do begin
        if ((not Trunked) or (not Zeroed[j])) then begin
                B[i,j] := B[i,j] + RBig[i,j];
             end; {if j}
             end; {j}
             end; {j}
         end; {if not Trunked i}
         end;
   Inf:=B;
 {build from B and D the 'Fisher Hessian' and the vector of
  first derivitives eD including constraints}
  writeln ('The Gradient');
  for i := 1 to totvar do begin
     tally := 0.0;
    for j := 1 to totvar do begin
    eB [i,j] := -0.5 * B [i,j];
     tally := tally + eB[i,j] * Parms [j];
     end;
    eD [i] := 0.5 * SumD [i] + tally;
      writeln (i,eD[i]:8:4);
    eB [totvar + 1,i] := 0.0;
    eB [i,totvar + 1] := 0.0;
  end;
 {The output code that follows is for input to the asymptotic parametric
  bootstrap hypothesis testing algorithm}
    {    for i := 1 to totvar do
          writeln (Parms[i]:14:8);
         k := 0;
         for i := 1 to totvar do begin
          if not Zeroed[i] then begin
         for j := 1 to totvar do begin
          if not Zeroed[j] then begin
           k := k + 1;
           write (eB[i,j]:14:6);
            if k mod 5 = 0 then writeln;
       end;
       end;
       end;
       end;
   halt;}
if feasible
 then begin
  for j := 1 to ncut do begin {ncut is number of cutting plane constraints}
    eD [totvar + j] := 0.0;
    for i := 1 to totvar do begin
    eD [totvar + j] := eD [totvar + j] + Parms[i] * cvec[i,aset[j]];
    eD [i] := eD [i] + lln[aset[j]] * cvec[i,aset[j]];
    eB [totvar + j, i] := cvec[i,aset[j]];
    eB [i, totvar + j] := cvec[i,aset[j]];
    end;
   end; {j}
   for i := 1 to ncut do
    for j := 1 to ncut do
    eB[totvar+i,totvar+j]:= 0.0;
   writeln ('  We are holding ',ncut,'  Constraints ');
   if Trunked
   then begin
      s := 0;
      for i := 1 to totvar do begin
         t := 0;
         if not Zeroed[i]
         then begin
            s := s + 1;
            for j := 1 to totvar do begin
               if not Zeroed[j]
               then begin
                  t := t + 1;
                  eB[s,t] := eB[i,j];
                  end;
               end;
                for k := 1 to ncut do
            eB[s,t+k] := eB[i,totvar+k];
            end;
         end;{i.. now for the totvar+first etc rows..}
          for k := 1 to ncut do begin
            s := s + 1;
            t := 0;
            for j := 1 to totvar do begin
               if not Zeroed[j]
               then begin
                  t := t + 1;
                  eB[s,t] := eB[totvar+k,j];
                  end;
               end;
            for j := 1 to ncut do begin
              t := t + 1;
            eB[s,t] := eB[totvar+k,totvar+j];
            end; {j again}
          end; {k}
      end
   else s:= totvar + ncut;
   eMatrixInversion (eB, s);
   if Trunked
   then begin
      eC := eB;
      s := 0;
      for i := 1 to totvar do begin
         t := 0;
         if not Zeroed[i]
         then begin
            s := s + 1;
            for j := 1 to totvar do begin
               if not Zeroed[j]
               then begin
                  t := t + 1;
                  eB[i,j] := eC[s,t];
                  end
               else eB[i,j] := 0.0;
               end;{j}
             for k := 1 to ncut do
             eB[i,totvar+k] := eC[s,t+k];
            end {if not Zeroed i }
         else begin
            for j := 1 to totvar + ncut do
               eB[i,j] := 0.0;
            end;{else}
         end; {i}
          for k := 1 to ncut do begin
            t := 0;
            s := s + 1;
            for j := 1 to totvar do begin
               if not Zeroed[j]
               then begin
                  t := t + 1;
                  eB[totvar+k,j] := eC[s,t];
                  end {if not Zeroed j}
               else eB[totvar+k,j] := 0.0;
               end; {j}
               for j := 1 to ncut do
             eB[totvar+k,totvar+j] := eC[s,t+j];
          end; {k}
      end; {if trunked}
    end {feasible}
    else begin
      if Trunked
   then begin
      s := 0;
      for i := 1 to totvar do begin
         t := 0;
         if not Zeroed[i]
         then begin
            s := s + 1;
            for j := 1 to totvar do begin
               if not Zeroed[j]
               then begin
                  t := t + 1;
                  B[s,t] := B[i,j];
                  end;
               end;
            end;
         end;
      end
   else s:= totvar;
   MatrixInversion (B, s);
   if Trunked
   then begin
      C := B;
      s := 0;
      for i := 1 to totvar do begin
         t := 0;
         if not Zeroed[i]
         then begin
            s := s + 1;
            for j := 1 to totvar do begin
               if not Zeroed[j]
               then begin
                  t := t + 1;
                  B[i,j] := C[s,t];
                  end
               else B[i,j] := 0.0;
               end;
            end
         else begin
            for j := 1 to totvar do
               B[i,j] := 0.0;
            end;
         end;
      end;
    end; {if feasible else}
    writeln ('at newtheta');
    if feasible
    then begin
    eNewtheta (eD,eB,Parms,totvar,ncut,lln,aset);
    end
    else  Newtheta (SumD, Parms, totvar);
   end;

procedure CuttingPlane (var Parms: Parmvec; var cvec: info; var ncut: integer;
                        var lln: lagvec; var aset: active; 
                         var alldone: boolean; var cfactors: itriplet);

{ procedure CuttingPlane analyses the positive definiteness of the 
 matrix of variance and covariance components and constructs an 
 eigenvector constraint equation if the matrix
 has negative eigenvalues. The constraint equation defines a hyperplane
 which separates the most recent iterate from the feasible region.}

var a, v: info;
    d: Parmvec;
    k, i, j, l, rots, minind, n, mnp, rfact: integer;
    trace, mineig, mintrace: real;

 
procedure jacobi (var a: info; var n: integer; var d: Parmvec;
                  var v: info; var nrot: integer);
 {from numerical recipes}
label 99; {these guys love labels}
var j,iq,ip,i: integer;
    tresh,theta,tau,t,sm,s,h,g,c: real;
    b,z: Parmvec;
begin
  for ip := 1 to n do begin
   for iq := 1 to n do
    v[ip,iq] := 0.0;
  v[ip,ip] := 1.0;
  end;
  for ip := 1 to n do begin
   b[ip] := a[ip,ip];
   d[ip] := b[ip];
   z[ip] := 0.0;
  end;
  nrot := 0;
  for i := 1 to 50 do begin
   sm := 0.0;
   for ip := 1 to n-1 do
    for iq := ip+1 to n do
     sm := sm+abs(a[ip,iq]);
    if sm = 0 then goto 99;
  if i < 4 then tresh := 0.2 * sm/sqr(n)
  else tresh := 0.0;
  for ip := 1 to n-1 do begin
   for iq := ip + 1 to n do begin
    g := 100.0 * abs (a[ip,iq]);
    if (i>4) and (abs(d[ip])+g = abs(d[ip]))
     and (abs(d[iq])+g = abs(d[iq])) then a[ip,iq] := 0.0
    else if abs(a[ip,iq]) > tresh
      then begin
       h := d[iq]-d[ip];
       if abs(h)+g = abs(h) then
        t := a[ip,iq]/h
        else begin
        theta := 0.5*h/a[ip,iq];
        t := 1.0/(abs(theta)+sqrt(1.0+sqr(theta)));
        if theta < 0.0 then t := -t;
       end;
        c := 1.0/sqrt(1+sqr(t));
        s := t * c;
        tau := s/(1.0+c);
        h := t*a[ip,iq];
        z[ip] := z[ip] - h;
        z[iq] := z[iq] + h;
        d[ip] := d[ip] - h;
        d[iq] := d[iq] + h;
        a[ip,iq] := 0.0;
         for j := 1 to ip-1 do begin
          g := a[j,ip];
          h := a[j,iq];
          a[j,ip] := g-s*(h+g*tau);
          a[j,iq] := h+s*(g-h*tau);
         end;
         for j := ip + 1 to iq-1 do begin
          g := a[ip,j];
          h := a[j,iq];
          a[ip,j] := g-s*(h+g*tau);
          a[j,iq] := h+s*(g-h*tau);
         end;
         for j := iq + 1 to n do begin
          g := a[ip,j];
          h := a[iq,j];
          a[ip,j] := g-s*(h+g*tau);
          a[iq,j] := h+s*(g-h*tau);
         end; 
         for j := 1 to n do begin
          g := v[j,ip];
          h := v[j,iq];
          v[j,ip] := g-s*(h+g*tau);
          v[j,iq] := h+s*(g-h*tau);
         end;
         nrot := nrot + 1;
        end;
       end;
      end;
      for ip := 1 to n do begin
       b[ip] := b[ip] + z[ip];
       d[ip] := b[ip];
       z[ip] := 0.0;
      end;
    end;
    writeln('error in subroutine jacobi  ');
    writeln('too many iterations  ');
    halt;
 99:
 end;

begin  {CuttingPlane}
 mnp := 3 * (nchar * (nchar + 1)) div 2;
 n := 3 * nchar;
 l := 0;
{make the matrix up}
 {zero it first}
 for i := 1 to mnp do
  for j := 1 to mnp do
  a[i,j] := 0.0;
 for k := 1 to 3 do begin
  for i := (k-1)*nchar+1 to k*nchar do begin
   for j := i to k*nchar do begin 
   l := l + 1;
   a[i,j] := Parms[l];
   a[j,i] := a[i,j];
   end; {j}
  end;{i}
  end;{k}
 jacobi (a,n,d,v,rots);
  mineig := 0.0;
  trace := 0.0;
 writeln ('The eigenvalues ');
 for i := 1 to n do begin
  trace := trace + d[i];
  write (d[i]:10:4);
  if d[i] < mineig then begin
   mineig := d[i];
  minind := i;
  end;
 end;
 writeln;
 if (mineig > 0) or (abs(mineig/trace) <  epsilon * 0.01) then begin
  alldone := true;
  writeln ('v-cv matrix is pos def (to specified tolerance) ');
 for i := 1 to ncut do begin
   writeln (Analysis, 'Constraint equation number ',i:5);
   for j := 1 to mnp do begin
    write (Analysis, cvec[j,aset[i]]:10:6);
    if j mod 5 = 0 then writeln (Analysis);
   end;
   writeln (Analysis);
  end; {i}
  end {pos def}
  else begin
  writeln ('v-cv matrix is not pos def');
  writeln (' min eigenvalue is ',mineig:10:4);
 {Just where will this constraint be applied?  How many other constraints are there?}
  if minind mod nchar > 0 then
  rfact := minind div (nchar) + 1
  else
  rfact := minind div nchar;
  cfactors[rfact] := cfactors[rfact]+1;
  {now make up constraint equation }
  l := 0;
 for k := 1 to 3 do begin
  for i := (k-1)*nchar+1 to k*nchar do begin
   for j := i to k*nchar do begin 
    l := l + 1;
    cvec[l,tncut+1] := v[i,minind]*v[j,minind];
    if not (i = j) then
    cvec[l,tncut+1] := 2 * cvec[l,tncut+1]; 
   end;
  end;
 end;
 tncut := tncut + 1;
 aset[ncut+1] := tncut;
{deal with the case that the new cutting plane overconstrains a random factor}
 if cfactors[rfact] > (nchar * (nchar + 1)/2) then begin
  {find the closest constraint for temp delete}
 minind := 0;
 mintrace := 1.0;
 for j := 1 to ncut do begin
  trace := 0.0;
  for i := 1 to mnp do
   trace := trace + sqr(abs(cvec[i,aset[j]])-abs(cvec[i,aset[ncut+1]]));
  if (trace < mintrace) then begin
   mintrace := trace;
   minind := j;
  end;
  end;{j}
  writeln ('the new cutting plane normal is close to the constraint ',aset[minind]:5);
  writeln ('we have replaced it');
  aset[minind] := aset[ncut + 1];
  cfactors[rfact] := cfactors[rfact]-1; {because of substitution}
  end {overconstraint}
  else begin
   ncut := ncut+1;
   lln[aset[ncut]] := 50.0;
  end;
 end; {else not pos def}
end; {procedure CuttingPlane} 
        

procedure Test ( Old: real; Current: real; var Maxed, better: boolean);

   {Compares the absolute value of the difference between the current
   and last loglikelihood to epsilon, the stopping criterion, to determine
   whether a maximum has been reached.}

   var diff: real;

   begin
      diff := Old-Current;
      if (diff<0)
      then better := true;
      diff := abs(diff);
      if diff < epsilon then Maxed := true
       else Maxed := false;
      end;

procedure Trunck (var Parms: Parmvec);
   var i: integer;
       totvar: integer;
   begin
      totvar := vartypes*((nchar*(nchar+1)) div 2);
      for i := 1 to totvar do
        if Zeroed[i]
        then Parms[i] := 0.0;
      end;

procedure Report;
   var i, j, k, l, s, t: integer;
       totvar: integer;
       count: integer;
       C: info;

   begin
    totvar := vartypes * ((nchar* (nchar + 1)) div 2);
    writeln (Analysis,'    At iteration ',Iter:4);
    writeln (Analysis);
    if Trunked or (ncut > 0)
    then write (Analysis,'   *** The constrained analysis converged ')
    else write (Analysis,'   *** The unconstrained analysis converged ');
    writeln (Analysis,'with the following results ***');
    writeln (Analysis,'   The log likelihood is ', LogLike:8:4);
    writeln (Analysis,'   The mean of each trait is');
    for i := 1 to nchar do
       writeln (Analysis, '   ',Means[i]:14:6);
    writeln (Analysis,'   The effect of the fixed factors is');
    writeln (Analysis,'   (in the order given, levels within factors)');
     count := nchar;
      for i := 1 to nfxfact do begin
       for j := 1 to nfxlevels[i] do begin
        for k := 1 to nchar do begin
     if (j=1){modified by rgs 7/16/92}
     then begin
     writeln (Analysis,'Factor: ',i:4,' Level: ',j:4,' Label: ',levels[i,j]:4);
         writeln (Analysis,'has fixed factor effect  0');
         end
     else begin
        count := count + 1;
        writeln (Analysis,'Factor: ',i:4,' Level: ',j:4);
        writeln (Analysis,' Label: ',levels[i,j]:4);
         writeln (Analysis,'has fixed factor effect  ',Means[count]:14:6);
         end;
       end; {k}
     end; {j}
   end; {i}
    writeln (Analysis);
    write (Analysis,'   The estimates of the');
    writeln (Analysis,' components are:');
    writeln (Analysis, '    Additive');
    writeln (Analysis,'              ');
    l := 1;
    for i := 1 to nchar do begin
       for j := i to nchar do begin
	  write (Analysis, Parms[l]:14:6);
          l := l+1;
          end;
       writeln(Analysis);
       for j := 1 to i do
       write (Analysis,'              ');
       end;
    writeln(Analysis);
    writeln (Analysis, '   Environmental');
    writeln (Analysis,'              ');
    for i := 1 to nchar do begin
       for j := i to nchar do begin
          write (Analysis, Parms[l]:14:6);
          l := l+1;
          end;
       writeln(Analysis);
       for j := 1 to i do
       write (Analysis,'              ');
       end;
    writeln(Analysis);
    if ceo = 1 then
    writeln (Analysis, '   Dominance')
    else writeln (Analysis, '   Common Environment');
    writeln (Analysis,'              ');
    for i := 1 to nchar do begin
       for j := i to nchar do begin
          write (Analysis, Parms[l]:14:6);
          l := l+1;
          end;
       writeln(Analysis);
       for j := 1 to i do
       write (Analysis,'              ');
       end;
    writeln (Analysis);
    writeln (Analysis,'    Large-sample var-cov matrix of the estimates');
    if feasible then begin {We need to invert the B matrix here since the 
                            feasibility algorithm uses Largrange multipliers}
    if Trunked then begin
      s := 0;
      for i := 1 to totvar do begin
       t := 0;
       if not Zeroed[i] then begin
         s := s + 1;
         for j := 1 to totvar do begin
          if not Zeroed[j] then begin
           t := t + 1;
           B[s,t] := B[i,j];
          end;
         end;
        end;
       end;
      end
   else s:= totvar;
   MatrixInversion (B, s);
   if Trunked then begin
    C := B;
    s := 0;
    for i := 1 to totvar do begin
     t := 0;
     if not Zeroed[i] then begin
      s := s + 1;
      for j := 1 to totvar do begin
       if not Zeroed[j] then begin
        t := t + 1;
        B[i,j] :=  C[s,t];
       end
       else B[i,j] := 0.0;
      end;
     end
     else begin
      for j := 1 to totvar do
      B[i,j] := 0.0;
     end;
    end;
   end;
   end; {if feasible}
   for i := 1 to totvar do begin
        for j := i to totvar do begin
           B[i,j] := 2.0 * B[i,j]; {Searle et al 6.95}
           write (Analysis,B[i,j]:14:6);
        end;
        writeln (Analysis);
        for j := 1 to i do
	   write (Analysis,'              ');
        end;
       writeln (Analysis);
       write (Analysis,'  The test statistic comparing two likelihoods is ');
       writeln (Analysis,'given by twice');
       write (Analysis, '  their difference and is compared to ');
       writeln (Analysis,'Chi-square with df given by the ');
       write (Analysis, '  number of parameters ');
       writeln (Analysis, 'specified by the hypothesis.');
    end;

procedure Cleanup (var hypo: Parmvec; var lln: lagvec;
                   var charnum: integer; var REML: boolean;
                   var ntrnc: integer; var tvec: Parmbool; 
		   var nfxfact: integer; var feasible: boolean);

   {reads and writes the parameters governing the simulation run}

   var Analtype, feas: integer;
      nvc, totvar, i, j, k, index : integer;
      stv: integer;
   begin
      for i := 1 to maxnparm do
	 tvec[i] := false;
      read (sibships, Analtype, charnum, nfxfact, feas, stv);
      writeln (Analtype);
      writeln ('Read charnum. It is ', charnum:4);
      nvc := (charnum * (charnum+1)) div 2;
      totvar := 3 * nvc;
      writeln ('Total number of (co)variances: ', totvar:4);
      if stv = 1 then writeln ('Starting values will be read after line 1 in sibships');
      index := 0;
      for k := 1 to 3 do begin {starting values give I for first V matrix}
       for i := 1 to nchar do begin
        for j := i to nchar do begin
         index := index + 1;
         if stv = 1 then read (sibships,hypo[index])
         else begin
          if (k = 2) and (i = j) then
           hypo[index] := 1
          else
           hypo[index] := 0;
         end;
        end; 
       end;
      end;{k}
      readln (sibships);
      if Analtype = 2
      then REML:=true
      else REML := false;
      if feas = 1
      then begin
      for i := 1 to nconstr do 
      lln[i] := 50.0;
      feasible:= true;
      writeln ('Feasibility constraints will be applied');
      end
      else feasible := false;
      if REML
      then writeln (Analysis,'  This is an REML analysis.')
      else writeln (Analysis,'  This is an ML analysis.');
      if ceo = 1 
       then writeln ('If not constrained, dominance effects will be estimated.')
       else begin
      if ceo = 4 
       then writeln ('If not constrained, common environment effects will be estimated.')
      else writeln ('Warning ** at the top of the program, ceo =',ceo,'  which is unusual!');
       end;
      read (sibships, ntrnc);
      writeln ('Read ntrnc. It is ', ntrnc:4);
      for i := 1 to ntrnc do begin
         read (sibships, index);
         tvec[index] := true;
         writeln (' index of the component to be tested against 0 ', index:6);
         end;
      readln (sibships);
      end;

procedure testkt (var lln: lagvec; var aset: active; var ncut: integer; 
                   var cvec: info; var llpos: boolean; var cfactors: itriplet);

{Tests if Kuhn-Tucker conditions hold (ie are the multipliers all positive)
 If there are negative multipliers, these constraint equations are dropped
 from the active set.  If inactive constraints are violated, add them
 back in again} 

var i, j, k, mnp, minind : integer;
    sum, minsum, mintrace, trace: real;
    flag, flag1, flag2: boolean;

begin
 flag1 := false;
 flag2 := false;
 mnp := 3 * nchar * (nchar + 1) div 2; {in case maxnparm is set too high}
 llpos := true;
 {check inactive constraints, if any, to make sure they're slack}
 if ncut < tncut then begin
  minsum := 0.0;
  for i := 1 to tncut do begin
   sum := 0.0;
   flag := true;
   for j := 1 to ncut do
    if aset[j] = i then flag := false;
  {don't worry if i is active}
   if flag then begin
    for j := 1 to mnp do 
     sum := sum + Parms[j] * cvec[j,i];
    if sum < minsum then begin
      minsum := sum;
      minind := i
    end;
   end; {flag}
  end; {i}
  if minsum < -0.02 * epsilon then begin
   ncut := ncut + 1;
   aset[ncut] := minind;
   lln[aset[ncut]] := 5.0; {nice and positive to start out with!}
   writeln ('Inactive constraint number ',minind,' is no longer slack.');
   writeln ('Value is ',minsum:14:6);
   writeln ('It will be added to the active set of constraints.');
   llpos := false;
  {find out which factor we're dealing with}
   for i := 1 to mnp do begin
    if (minsum < abs(cvec[i,aset[ncut]])) then begin
     minsum := abs(cvec[i,aset[ncut]]); {biggest component}
     minind := i;
    end; {if}
   end; {i}
    if minind mod (nchar * (nchar + 1) div 2) > 0 then 
    minind := minind div (nchar * (nchar + 1) div 2) + 1
    else
    minind := minind div (nchar * (nchar + 1) div 2);
   cfactors[minind] := cfactors[minind]+1;
  {overconstrained?}
  if cfactors[minind] > (nchar * (nchar + 1)/2) then begin
   {find the closest constraint for temp delete}
     cfactors[minind] := cfactors[minind]-1; {because of substitution}
     minind := 0;
     mintrace := 1.0;
     for j := 1 to ncut-1 do begin
      trace := 0.0;
      for i := 1 to mnp do
       trace := trace + sqr(abs(cvec[i,aset[j]])-abs(cvec[i,aset[ncut]]));
      if (trace < mintrace) then begin
       mintrace := trace;
       minind := j;
      end;
      end;{j}
      writeln ('the new cutting plane normal is close to the constraint ',minind:5);
      writeln ('we have replaced it');
      flag1 := true;
      aset[minind] := aset[ncut];
      ncut := ncut - 1;
    end; {cfactors too big}
   end; {minsum < 0.0}
  end; {inactive constraints}
 if not flag1 then begin
 k := 0;
 for i := 1 to ncut do begin
  k := k + 1;
  if lln[aset[k]] < 0 
  then begin
   writeln (' to satisfy k-t we will drop constraint ',aset[k]:5);
   flag2 := true;
 {adjust cfactors array}
   minsum := 0.0;
    for j := 1 to mnp do begin
     if (minsum < abs(cvec[j,aset[k]])) then begin
      minsum := abs(cvec[j,aset[k]]); {biggest component}
      minind := j;
     end; {if}
    end; {j}
    if minind mod (nchar * (nchar + 1) div 2) > 0 then 
    minind := minind div (nchar * (nchar + 1) div 2) + 1
    else
    minind := minind div (nchar * (nchar + 1) div 2);
    cfactors[minind] := cfactors[minind]-1;
 {delete it from active set array}
   for j := k to ncut do
   aset[j] := aset[j+1];
   k := k - 1;
  end; {if}
 end; {i}
 ncut := k;
 end; {if not flag1}
 if flag1 or flag2 then
  llpos :=  false;  {boolean to force another round of iterations}
end; {proc}
begin {program nf3}
{unix initialization}
  assign(sibships, 'sibships');
  reset(sibships);
  assign(Analysis, 'analysis');
  rewrite(Analysis);

{Vax initialization} 
  {open ( sibships, 'sibships', history := readonly );
  reset( sibships );
  open ( Analysis, 'Analysis', history := new );
  rewrite ( Analysis );  }
   ncut := 0;
   tncut := 0;
   Iter := 0;
   Done := false;
   Trunked := false;
   Maxed := false;
   Cleanup (Parms, lln, nchar, REML, ntrunc, Zeroed, nfxfact, feasible);
   if ntrunc>0 then begin
      Trunked := true;
      end;
   if feasible then begin {initialize constraint counter}
    for I := 1 to 3 do 
     cfactors[I] := 0;
   end;
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
	    Visit (PresentData[I], famnum);
	    end;
	 end;
      end;
   writeln ('The program has found ',famnum:10,' families');
   if famnum > f then begin
     writeln ('The constant f is too low.');
  { PrintFams(PresentData, Zmatrix);}
     halt;
   end;
  { PrintFams(PresentData, Zmatrix);}
   Collecthem(PresentData,Fm,famsize);
   Designit (PresentData,Fm,Zmatrix,vert,Design,DataVec);
   if Trunked
   then Trunck(Parms);
   ZeroEmpty (Empty);
   alldone := false;
   restart := false;
   OldLogLike := -9900;
  repeat
   repeat
    if not restart then begin
         EnterValues (AddCov, DomCov, EnvCov);
         MakeCovArray (Q);
         Iter := Iter + 1;
         vartypes := 3;
         better:=true;
	 ok := true;
	 writeln ('starting comploglike');
         ComputeLogLikelihood (LogLike, Q, Means, XVXInv, Py, vert, DataVec,
	                       Design, ok);
	 writeln ('done comploglike');
      if Iter > 1 then 
      Test(OldLogLike, LogLike, Maxed, better);
      if Maxed 
      then begin
        testkt (lln,aset,ncut,cvec,llpos,cfactors);
        if llpos then Done := true; {not done unless the lm's are positive}
      end; {Maxed}
      OldLogLike := LogLike;
   end; {not restart, otherwise begin here}
      if not Done
      then begin
      CalcNewEsts (Parms,lln,aset,Inf,B,ncut);
      restart := false;
      end;
      if Iter=maxround
      then begin
         writeln ('Exceeded max number of iterations without converging.');
         Done := true;
         alldone := true;
         end;
    until Done;
    if feasible then
    CuttingPlane (Parms,cvec,ncut,lln,aset,alldone,cfactors)
    else alldone := true;
    if not alldone then begin
     restart := true;
     Done := false;
     Iter := 1;
    end;
   until alldone;
   Report;
end {program nf3}.


