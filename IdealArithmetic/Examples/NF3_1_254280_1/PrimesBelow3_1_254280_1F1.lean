
import IdealArithmetic.Examples.NF3_1_254280_1.RI3_1_254280_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [33, 27, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 34, 21], [8, 2, 16], [0, 1]]
 g := ![![[11, 22, 30], [15, 11], [28, 27, 21], [15, 1], []], ![[14, 16, 0, 3], [36, 27], [21, 28, 19, 3], [34, 4], [14, 34]], ![[13, 0, 21, 3], [1, 3], [26, 2, 15, 36], [22, 9], [19, 34]]]
 h' := ![![[7, 34, 21], [24, 30, 20], [1, 29, 14], [23, 6, 13], [0, 0, 1], [0, 1]], ![[8, 2, 16], [3, 2, 4], [9, 7, 8], [24, 27, 4], [31, 12, 2], [7, 34, 21]], ![[0, 1], [30, 5, 13], [10, 1, 15], [4, 4, 20], [29, 25, 34], [8, 2, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 31], []]
 b := ![[], [23, 14, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [33, 27, 22, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-247197, -60310, -5735]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6681, -1630, -155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [33, 12, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 27, 10], [12, 13, 31], [0, 1]]
 g := ![![[40, 7, 2], [9, 16], [38, 2], [4, 4, 1], []], ![[24, 26, 9, 32], [19, 32], [2, 31], [24, 24, 5, 9], [38, 18]], ![[28, 0, 7, 20], [21, 37], [36, 16], [30, 32, 37, 8], [17, 18]]]
 h' := ![![[33, 27, 10], [0, 35, 24], [16, 12, 37], [32, 25, 17], [0, 0, 1], [0, 1]], ![[12, 13, 31], [24, 22, 6], [6, 20, 27], [20, 40, 20], [40, 35, 13], [33, 27, 10]], ![[0, 1], [6, 25, 11], [24, 9, 18], [8, 17, 4], [34, 6, 27], [12, 13, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 15], []]
 b := ![[], [9, 39, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [33, 12, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1036767, 192126, 11316]
  a := ![-1, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25287, 4686, 276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2024397742711, -620637238650, -148646332024]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-2024397742711, -620637238650, -148646332024]] 
 ![![43, 0, 0], ![0, 43, 0], ![8, 35, 1]] where
  M :=![![![-2024397742711, -620637238650, -148646332024], ![13378169882160, 379995480227, -2159204379998], ![69235521360660, 13096207480712, -1779208899771]]]
  hmulB := by decide  
  f := ![![![-641890632870309070890013, 70952244278336897331866, -32478315776846185614236]], ![![2923048419916156705281240, -323103087826491740851047, 147900101281318320767126]], ![![2179277117882996466584572, -240889326779544266645887, 110266837955492984229107]]]
  g := ![![![-19423885733, 106557776330, -148646332024], ![712832672608, 1766329041399, -2159204379998], ![1941144012996, 1752756255179, -1779208899771]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [12, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 42], [0, 1]]
 g := ![![[26, 21], [15, 1], [13], [8, 35], [1]], ![[10, 22], [4, 42], [13], [10, 8], [1]]]
 h' := ![![[32, 42], [35, 35], [30, 42], [33, 23], [31, 32], [0, 1]], ![[0, 1], [37, 8], [41, 1], [38, 20], [23, 11], [32, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [24, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [12, 11, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3404, -222, 189]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, -159, 189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-641890632870309070890013, 70952244278336897331866, -32478315776846185614236]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-641890632870309070890013, 70952244278336897331866, -32478315776846185614236]] 
 ![![43, 0, 0], ![22, 1, 0], ![18, 0, 1]] where
  M :=![![![-641890632870309070890013, 70952244278336897331866, -32478315776846185614236], ![2923048419916156705281240, -323103087826491740851047, 147900101281318320767126], ![-3462653565134164054586700, 382749068180112285358576, -175202986545173420083921]]]
  hmulB := by decide  
  f := ![![![-2024397742711, -620637238650, -148646332024]], ![![-724618150174, -308698227211, -126265667082]], ![![762706092834, 44761329884, -103600997121]]]
  g := ![![![-37633263325825336538019, 70952244278336897331866, -32478315776846185614236], ![171374756489191749539442, -323103087826491740851047, 147900101281318320767126], ![-203011146681011924906158, 382749068180112285358576, -175202986545173420083921]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-2024397742711, -620637238650, -148646332024]] ![![-641890632870309070890013, 70952244278336897331866, -32478315776846185614236]]
  ![![43, 0, 0]] where
 M := ![![![43, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-369121594596796284408424337, -122178210162447836460045650, -34712433092345720422280366]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-369121594596796284408424337, -122178210162447836460045650, -34712433092345720422280366]] 
 ![![47, 0, 0], ![9, 1, 0], ![23, 0, 1]] where
  M :=![![![-369121594596796284408424337, -122178210162447836460045650, -34712433092345720422280366], ![3124118978311114838005232940, 169605812673800197118985705, -435959496672034950224697682], ![14120157892931420119409341440, 2785210979458511413567201708, -266353683998234753105711977]]]
  hmulB := by decide  
  f := ![![![-1169064043696976934066194607744397422493144626903752071, 129224066153598813142251885965776121394863620021815178, -59152181431223075451523203281922939142164872225351330]], ![![-110593192860908842892737514347372601694541768975577637, 12224567291627456946597849348189081241951974467552879, -5595782920907604054042544217102637582536653923689768]], ![![-706275375107325231397618242971658023831600291924851999, 78069098342043910887716010007161894100973722655389734, -35736048297780410396840265499528582735139589910418915]]]
  g := ![![![32529111872110336456264573, -122178210162447836460045650, -34712433092345720422280366], ![247334789100079083385157623, 169605812673800197118985705, -435959496672034950224697682], ![-102566089153952835771576563, 2785210979458511413567201708, -266353683998234753105711977]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-373038663979765984464283, -86585346355546716111346, -3940081064644078180385]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-373038663979765984464283, -86585346355546716111346, -3940081064644078180385]] 
 ![![47, 0, 0], ![13, 1, 0], ![42, 0, 1]] where
  M :=![![![-373038663979765984464283, -86585346355546716111346, -3940081064644078180385], ![354607295817967036234650, -239172344848490330188317, -267636201195928304694808], ![8147288467817171486255790, 1188747236723035564190782, -506808546044418634883125]]]
  hmulB := by decide  
  f := ![![![439366382965407841987461299006402970724532310481, -48565953973267437109694914053959663622746647320, 22231014750708178113290652101504952617330529523]], ![![78956843638012040758315706339314742209769625089, -8727600887708500865709904145939838811838166205, 3995050198740858731282447645972240391313148955]], ![![443053885416541759003186343276379760870591651956, -48973557015424125140338131946297406556190628542, 22417594617904992923263241237162598451779062991]]]
  g := ![![![19533069007604098054455, -86585346355546716111346, -3940081064644078180385], ![312863153810155960124781, -239172344848490330188317, -267636201195928304694808], ![297436879240070038656742, 1188747236723035564190782, -506808546044418634883125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-575161442363, -3240784228, 103885002140]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-575161442363, -3240784228, 103885002140]] 
 ![![47, 0, 0], ![24, 1, 0], ![4, 0, 1]] where
  M :=![![![-575161442363, -3240784228, 103885002140], ![-9349650192600, -1818540683815, 198047651596], ![-9057979612080, -3908740670584, -1620493032219]]]
  hmulB := by decide  
  f := ![![![-3721049417435918524687549, 411311201188723106091692, -188277273124113582536212]], ![![-1539579392282804726898768, 170179478455193104379913, -77899478673633698460988]], ![![-743771302033160238696668, 82213761046947474205160, -37633263325825336538019]]]
  g := ![![![-19423885733, -3240784228, 103885002140], ![712832672608, -1818540683815, 198047651596], ![1941144012996, -3908740670584, -1620493032219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-369121594596796284408424337, -122178210162447836460045650, -34712433092345720422280366]] ![![-373038663979765984464283, -86585346355546716111346, -3940081064644078180385]]
  ![![-188440864042258638303366395671427306855852998136269, 19917861210960375734349538116491131610238708112440, 51746238787413263506834406884503823154015300238695]] where
 M := ![![![-188440864042258638303366395671427306855852998136269, 19917861210960375734349538116491131610238708112440, 51746238787413263506834406884503823154015300238695]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![-188440864042258638303366395671427306855852998136269, 19917861210960375734349538116491131610238708112440, 51746238787413263506834406884503823154015300238695]] ![![-575161442363, -3240784228, 103885002140]]
  ![![47, 0, 0]] where
 M := ![![![-546557491682772927391051731494224481673627707849174667098015953, -237873372864726812158742850368975400473697208207525081103241148, -99485913325191473652229539451139964120554781381188600188675625]]]
 hmul := by decide  
 g := ![![![![-11628882801761126114703228329664350673906972507429248236127999, -5061135592866527918271124475935646818589302302287767683047684, -2116721560110456886217649775556169449373505986833800004014375]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9443049631766019860232183128271349, 1043800189464508581270177287156156, -477798447479282675404180088293012]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-9443049631766019860232183128271349, 1043800189464508581270177287156156, -477798447479282675404180088293012]] 
 ![![53, 0, 0], ![0, 53, 0], ![17, 9, 1]] where
  M :=![![![-9443049631766019860232183128271349, 1043800189464508581270177287156156, -477798447479282675404180088293012], ![43001860273135440786376207946371080, -4753268451479136336652199355911361, 2175803673434960393002171684882444], ![-50940156778670331527939747897682960, 5630738730638638690116715909260584, -2577464778044175943650027671028917]]]
  hmulB := by decide  
  f := ![![![-49109549247491297, -5471633013515548, 4484743021448756]], ![![-403626871930388040, -97454832491360821, -7445412997649132]], ![![-82616680854619493, -20280601741601469, -1805062851004213]]]
  g := ![![![-24914641973928573176624936363965, 100829928618453823771845246826288, -477798447479282675404180088293012], ![113456562730964417081873383082444, -459160405894222261767391406034969, 2175803673434960393002171684882444], ![-134401048149421518601684480947007, 543923051566721173263527640538129, -2577464778044175943650027671028917]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [30, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 52], [0, 1]]
 g := ![![[22, 43], [15], [12, 15], [44], [29, 1]], ![[50, 10], [15], [23, 38], [44], [5, 52]]]
 h' := ![![[29, 52], [42, 34], [11, 42], [12, 42], [31, 16], [0, 1]], ![[0, 1], [21, 19], [10, 11], [11, 11], [18, 37], [29, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [39, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [30, 24, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1385, -1787, -917]
  a := ![1, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![268, 122, -917]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49109549247491297, 5471633013515548, -4484743021448756]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![49109549247491297, 5471633013515548, -4484743021448756]] 
 ![![53, 0, 0], ![24, 1, 0], ![28, 0, 1]] where
  M :=![![![49109549247491297, 5471633013515548, -4484743021448756], ![403626871930388040, 97454832491360821, 7445412997649132], ![-88820099286011280, 104760638652866152, 104900245489009953]]]
  hmulB := by decide  
  f := ![![![9443049631766019860232183128271349, -1043800189464508581270177287156156, 477798447479282675404180088293012]], ![![3464742092249981808664079002493232, -382979926333378671959095387468611, 175308661623921204088644347814148]], ![![5949915971096582785178129726212844, -657681962936695829541163772634584, 301053232216303601037114531004401]]]
  g := ![![![818172858937421, 5471633013515548, -4484743021448756], ![-40448314562197120, 97454832491360821, 7445412997649132], ![-104533628314095804, 104760638652866152, 104900245489009953]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-9443049631766019860232183128271349, 1043800189464508581270177287156156, -477798447479282675404180088293012]] ![![49109549247491297, 5471633013515548, -4484743021448756]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95326842262633043364460051207548517541758291, 10537080699022123086576212875013971501978234, -4823337694103639703892583089191780705594383]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-95326842262633043364460051207548517541758291, 10537080699022123086576212875013971501978234, -4823337694103639703892583089191780705594383]] 
 ![![59, 0, 0], ![0, 59, 0], ![51, 8, 1]] where
  M :=![![![-95326842262633043364460051207548517541758291, 10537080699022123086576212875013971501978234, -4823337694103639703892583089191780705594383], ![434100392469327573350332478027260263503494470, -47983870632411490004325267012261120576603929, 21964566708859089851943472446658353094745936], ![-514236870442663504441526680723997171674546590, 56841863987672831709003602889120008788847746, -26019303923552400152381794565602767481857993]]]
  hmulB := by decide  
  f := ![![![-2463444293135100467699, -987807627566487205316, -377210045420035827563]], ![![33948904087803224480670, 3050883879471816668373, -3717842973539533271074]], ![![4556053632564792287319, 3670428587167691306, -841481613539081525034]]]
  g := ![![![2553616612485636975153587904088683024467038, 832606478844936283351133518449969782148022, -4823337694103639703892583089191780705594383], ![-11628686604787898459301434182242639734382174, -3791532276326850996947000789585219412450363, 21964566708859089851943472446658353094745936], ![13775383553534049208982115968165152032206967, 4491462633493085303865389142609188960062910, -26019303923552400152381794565602767481857993]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [49, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 58], [0, 1]]
 g := ![![[35, 53], [54, 46], [4], [54, 27], [55, 1]], ![[0, 6], [47, 13], [4], [5, 32], [51, 58]]]
 h' := ![![[55, 58], [9, 17], [3, 20], [9, 2], [19, 26], [0, 1]], ![[0, 1], [0, 42], [41, 39], [1, 57], [33, 33], [55, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [21, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [49, 4, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-671, -509, -189]
  a := ![0, 1, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![152, 17, -189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2463444293135100467699, 987807627566487205316, 377210045420035827563]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![2463444293135100467699, 987807627566487205316, 377210045420035827563]] 
 ![![59, 0, 0], ![33, 1, 0], ![2, 0, 1]] where
  M :=![![![2463444293135100467699, 987807627566487205316, 377210045420035827563], ![-33948904087803224480670, -3050883879471816668373, 3717842973539533271074], ![-122851590568787072959110, -26187673256759207911186, 666959094067716602701]]]
  hmulB := by decide  
  f := ![![![95326842262633043364460051207548517541758291, -10537080699022123086576212875013971501978234, 4823337694103639703892583089191780705594383]], ![![45960769528772251825031342573251539243636087, -5080335465005399522926945048528812525231827, 2325518257568830853839182533841871359150317]], ![![11947297541829315104583843782018545877255308, -1320610599757916574273830993883863589708546, 604508123928130162036728148203158116831301]]]
  g := ![![![-523536059447441507845, 987807627566487205316, 377210045420035827563], ![1004992847248943373449, -3050883879471816668373, 3717842973539533271074], ![12542503537561548388214, -26187673256759207911186, 666959094067716602701]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-95326842262633043364460051207548517541758291, 10537080699022123086576212875013971501978234, -4823337694103639703892583089191780705594383]] ![![2463444293135100467699, 987807627566487205316, 377210045420035827563]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 4, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![11, 4, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![11, 4, 1]] where
  M :=![![![11, 4, 1], ![-90, -5, 14], ![-450, -86, 9]]]
  hmulB := by decide  
  f := ![![![-19, 2, -1]], ![![90, -9, 4]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-4, -1, 14], ![-9, -2, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [11, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 60], [0, 1]]
 g := ![![[44, 15], [12], [34, 16], [26, 25], [4, 1]], ![[43, 46], [12], [37, 45], [4, 36], [8, 60]]]
 h' := ![![[4, 60], [54, 36], [53, 16], [19, 57], [17, 5], [0, 1]], ![[0, 1], [15, 25], [56, 45], [3, 4], [37, 56], [4, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [26, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [11, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39531, -17924, -3627]
  a := ![1, -1, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, -56, -3627]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 2, -1]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-19, 2, -1]] 
 ![![61, 0, 0], ![47, 1, 0], ![52, 0, 1]] where
  M :=![![![-19, 2, -1], ![90, -9, 4], ![-90, 14, -5]]]
  hmulB := by decide  
  f := ![![![11, 4, 1]], ![![7, 3, 1]], ![![2, 2, 1]]]
  g := ![![![-1, 2, -1], ![5, -9, 4], ![-8, 14, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![11, 4, 1]] ![![-19, 2, -1]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![121131595131858210961112101868954761, -13389443758025205076674928513092864, 6129003907805040921675886286242311]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![121131595131858210961112101868954761, -13389443758025205076674928513092864, 6129003907805040921675886286242311]] 
 ![![67, 0, 0], ![0, 67, 0], ![41, 40, 1]] where
  M :=![![![121131595131858210961112101868954761, -13389443758025205076674928513092864, 6129003907805040921675886286242311], ![-551610351702453682950829765761807990, 60972991996222924977676394947139893, -27910323458465533386673012966793970], ![653439586519814773949913800416549770, -72228823400289094103584536720093450, 33062668537757391591003381980345923]]]
  hmulB := by decide  
  f := ![![![76470795556965817, 33566113672818366, 14159513002277871]], ![![-1274356170205008390, -127009474143187001, 129017367023010840]], ![![-778123143151095499, -69328703929885172, 85720038908860450]]]
  g := ![![![-1942650225196245773546257251745970, -3858949254779505103637468357653512, 6129003907805040921675886286242311], ![8846461344696017700041250236966340, 17572924333355884484247715128640279, -27910323458465533386673012966793970], ![-10479549604899078825092908369815419, -20816948730008727727518206207969110, 33062668537757391591003381980345923]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [44, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 66], [0, 1]]
 g := ![![[50, 10], [54, 40], [9], [47], [54], [1]], ![[26, 57], [25, 27], [9], [47], [54], [1]]]
 h' := ![![[11, 66], [36, 55], [45, 24], [46, 64], [29, 28], [23, 11], [0, 1]], ![[0, 1], [38, 12], [41, 43], [13, 3], [2, 39], [10, 56], [11, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [40, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [44, 56, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11, 53, 3]
  a := ![-1, 1, 0]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -1, 3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76470795556965817, -33566113672818366, -14159513002277871]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-76470795556965817, -33566113672818366, -14159513002277871]] 
 ![![67, 0, 0], ![12, 1, 0], ![23, 0, 1]] where
  M :=![![![-76470795556965817, -33566113672818366, -14159513002277871], ![1274356170205008390, 127009474143187001, -129017367023010840], ![4295306400758661330, 940854858160379490, -2007892879823839]]]
  hmulB := by decide  
  f := ![![![-121131595131858210961112101868954761, 13389443758025205076674928513092864, -6129003907805040921675886286242311]], ![![-13462220744475296247500230696502226, 1488064673135515461827205182238425, -681160051271566532439367499524086]], ![![-51335317530635128747096897662724019, 5674418355744310609956834216734766, -2597459080854825862530578605431628]]]
  g := ![![![9731214441332024, -33566113672818366, -14159513002277871], ![40561819731582294, 127009474143187001, -129017367023010840], ![-103712990461640959, 940854858160379490, -2007892879823839]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![121131595131858210961112101868954761, -13389443758025205076674928513092864, 6129003907805040921675886286242311]] ![![-76470795556965817, -33566113672818366, -14159513002277871]]
  ![![67, 0, 0]] where
 M := ![![![-67, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1345382891, 613610964, 268587621]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1345382891, 613610964, 268587621]] 
 ![![71, 0, 0], ![0, 71, 0], ![66, 29, 1]] where
  M :=![![![1345382891, 613610964, 268587621], ![-24172885890, -2491279525, 2378008134], ![-79397872650, -17569661166, -113271391]]]
  hmulB := by decide  
  f := ![![![-592436448754063289, 65485759534181622, -29976038089709031]], ![![2697843428073812790, -298209751211736539, 136505202423126804]], ![![506208153047462826, -55954398913881815, 25613067712130585]]]
  g := ![![![-230723945, -101062395, 268587621], ![-2551005954, -1006387541, 2378008134], ![-1012985364, -201194237, -113271391]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [49, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 70], [0, 1]]
 g := ![![[68, 29], [30, 37], [25, 43], [29], [25], [1]], ![[0, 42], [2, 34], [27, 28], [29], [25], [1]]]
 h' := ![![[5, 70], [21, 10], [53, 26], [37, 55], [40, 61], [22, 5], [0, 1]], ![[0, 1], [0, 61], [41, 45], [28, 16], [61, 10], [47, 66], [5, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [39, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [49, 66, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1841, -1662, -72]
  a := ![0, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, 6, -72]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-592436448754063289, 65485759534181622, -29976038089709031]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-592436448754063289, 65485759534181622, -29976038089709031]] 
 ![![71, 0, 0], ![53, 1, 0], ![28, 0, 1]] where
  M :=![![![-592436448754063289, 65485759534181622, -29976038089709031], ![2697843428073812790, -298209751211736539, 136505202423126804], ![-3195874930002533190, 353260332998763714, -161704548788609735]]]
  hmulB := by decide  
  f := ![![![1345382891, 613610964, 268587621]], ![![663836723, 422959177, 233988057]], ![![-587706362, -5472594, 104326507]]]
  g := ![![![-45406375176814597, 65485759534181622, -29976038089709031], ![206772036259835195, -298209751211736539, 136505202423126804], ![-244942890321914612, 353260332998763714, -161704548788609735]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1345382891, 613610964, 268587621]] ![![-592436448754063289, 65485759534181622, -29976038089709031]]
  ![![71, 0, 0]] where
 M := ![![![71, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5764781356298167549, -637217859332605736, 291685810146658630]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![5764781356298167549, -637217859332605736, 291685810146658630]] 
 ![![73, 0, 0], ![0, 73, 0], ![50, 62, 1]] where
  M :=![![![5764781356298167549, -637217859332605736, 291685810146658630], ![-26251722913199276700, 2901769493870869725, -1328281957704499948], ![31097884426735239540, -3437446473581759108, 1573487536166369777]]]
  hmulB := by decide  
  f := ![![![569996917, 237779984, 95061986]], ![![-8555578740, -808526899, 903463924]], ![![-7286326210, -612402518, 833736981]]]
  g := ![![![-120815193849791287, -256462165594869052, 291685810146658630], ![550169520164735900, 1167880148925340637, -1328281957704499948], ![-651732772350455470, -1383474982409543634, 1573487536166369777]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [51, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 72], [0, 1]]
 g := ![![[51, 32], [8], [3], [38, 49], [72], [1]], ![[39, 41], [8], [3], [47, 24], [72], [1]]]
 h' := ![![[27, 72], [53, 55], [60, 9], [33, 52], [24, 66], [22, 27], [0, 1]], ![[0, 1], [5, 18], [11, 64], [50, 21], [54, 7], [21, 46], [27, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [28, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [51, 46, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2733, -904, -316]
  a := ![2, -2, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![179, 256, -316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-569996917, -237779984, -95061986]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-569996917, -237779984, -95061986]] 
 ![![73, 0, 0], ![31, 1, 0], ![55, 0, 1]] where
  M :=![![![-569996917, -237779984, -95061986], ![8555578740, 808526899, -903463924], ![29955777300, 6465715276, -94937025]]]
  hmulB := by decide  
  f := ![![![-5764781356298167549, 637217859332605736, -291685810146658630]], ![![-2088445193589642703, 230849097882738467, -105670933655368734]], ![![-4769326835933348695, 527183955299658556, -241317905400446499]]]
  g := ![![![164788929, -237779984, -95061986], ![454544667, 808526899, -903463924], ![-2263833697, 6465715276, -94937025]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![5764781356298167549, -637217859332605736, 291685810146658630]] ![![-569996917, -237779984, -95061986]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [12, 65, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 0, 61], [7, 78, 18], [0, 1]]
 g := ![![[34, 57, 23], [63, 3, 51], [3, 68, 51], [15, 48, 51], [73, 1], []], ![[61, 45, 64, 29], [34, 38, 30, 70], [31, 5, 32, 54], [15, 15, 37, 59], [29, 1], [31, 8]], ![[50, 67, 7, 51], [70, 47, 1, 16], [6, 31, 43, 65], [43, 64, 66, 62], [], [74, 8]]]
 h' := ![![[66, 0, 61], [34, 9, 24], [43, 26, 50], [57, 78, 50], [72, 62, 50], [0, 0, 1], [0, 1]], ![[7, 78, 18], [22, 54, 51], [62, 73, 35], [32, 73, 47], [18, 73, 19], [34, 22, 78], [66, 0, 61]], ![[0, 1], [27, 16, 4], [66, 59, 73], [49, 7, 61], [31, 23, 10], [30, 57], [7, 78, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 10], []]
 b := ![[], [43, 61, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [12, 65, 6, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27018, -158, 316]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![342, -2, 4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB143I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB143I1 : PrimesBelowBoundCertificateInterval O 31 79 143 where
  m := 11
  g := ![1, 1, 2, 3, 2, 2, 2, 2, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB143I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![5329, 73]
    · exact ![493039]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I43N1, I47N0, I47N1, I47N2, I53N1, I59N1, I61N1, I67N1, I71N1, I73N1]
  Il := ![[], [], [I43N1], [I47N0, I47N1, I47N2], [I53N1], [I59N1], [I61N1], [I67N1], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
