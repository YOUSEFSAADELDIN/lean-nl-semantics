concrete FraCaSEndToEndEng of FraCaSEndToEnd = FraCaSLogicEng **
  open ParadigmsEng, MorphoEng, ResEng, Prelude in {
  lincat
    EllAux = {s : Number => Str} ;
  lin
    forMoreThanTwoYears_Adv = mkAdv "for more than two years" ;
    forExactlyAYear_Adv = mkAdv "for exactly a year" ;
    -- See FraCaSEndToEnd.gf for why each of these three exists.
    who_RP = {
      s = table {
        RC _ (NCase Gen) | RC _ NPNomPoss => "whose" ;
        RC _ _ => "who" ;
        RPrep _ => "whom"
        } ;
      a = RNoAg
      } ;
    ExistNP np =
      mkClause "there" (agrP3 (fromAgr np.a).n)
        (insertObj (\\_ => np.s ! NPAcc) (predAux auxBe)) ;
    usedTo_VV = mkVV (mkV "used" "used" "used" "used" "using") ;
    UncNeg = {s = [] ; p = CNeg False} ;
    ElliptS np aux = {s = np.s ! npNom ++ aux.s ! (fromAgr np.a).n} ;
    SoS aux np = {s = "so" ++ aux.s ! (fromAgr np.a).n ++ np.s ! npNom} ;
    TooS s = {s = s.s ++ "too"} ;
    ellDid = {s = \\_ => "did"} ;
    ellDidnt = {s = \\_ => "didn't"} ;
    ellDoes = {s = table {Sg => "does" ; Pl => "do"}} ;
    ellHas = {s = table {Sg => "has" ; Pl => "have"}} ;
    anaphOne_N = mkN "one" "ones" ;
    anaphOne_NP = {s = \\_ => "one" ; a = agrP3 Sg} ;
    MoreThanNP cn np =
      {s = \\_ => "more" ++ cn.s ! Pl ! Nom ++ "than" ++ np.s ! npNom ; a = agrP3 Pl} ;
    MoreThanAux cn np aux =
      {s = \\_ => "more" ++ cn.s ! Pl ! Nom ++ "than" ++ np.s ! npNom ++ aux.s ! (fromAgr np.a).n ;
       a = agrP3 Pl} ;
    MoreThanV2 cn np v2 =
      {s = \\_ => "more" ++ cn.s ! Pl ! Nom ++ "than" ++ np.s ! npNom ++ v2.s ! VPast ++ v2.p ;
       a = agrP3 Pl} ;
    -- See FraCaSEndToEnd.gf for why each of these exists.
    seeDo_V2V = mkV2V (mkV "see" "sees" "saw" "seen" "seeing") noPrep noPrep ;
    AndEveryNP cn1 cn2 =
      {s = \\_ => "every" ++ cn1.s ! Sg ! Nom ++ "and" ++ "every" ++ cn2.s ! Sg ! Nom ;
       a = agrP3 Sg} ;
    floatAll_AdV = mkAdV "all" ;
    moreThan_AdN = mkAdN "more than" ;
    ComparCN a cn np =
      {s = \\n,c => a.s ! AAdj Compar Nom ++ cn.s ! n ! Nom ++ "than" ++ np.s ! npNom ;
       g = cn.g} ;
    GapS np adv = {s = np.s ! npNom ++ adv.s} ;
    GapS2 np adv1 adv2 = {s = np.s ! npNom ++ adv1.s ++ adv2.s} ;
    ElliptAdvS np aux adv = {s = np.s ! npNom ++ aux.s ! (fromAgr np.a).n ++ adv.s} ;
    FragAdvS adv = {s = adv.s} ;
    FragNPS np = {s = np.s ! npNom} ;
    AndS s = {s = "and" ++ s.s} ;
    ButS s = {s = "but" ++ s.s} ;
    CommaAndS s1 s2 = {s = s1.s ++ "," ++ "and" ++ s2.s} ;
    ThenS s = {s = "then" ++ s.s} ;
    ellGoingTo = {s = table {Sg => "is going to" ; Pl => "are going to"}} ;
    ComplVSBare v s = insertExtra s.s (predV v) ;
    currently_AdV = mkAdV "currently" ;
    ItIsNow np = {s = "it" ++ "is" ++ "now" ++ np.s ! npNom} ;
    y1996_PN = mkPN "1996" ;
    atAQuarterPastFive_Adv = mkAdv "at a quarter past five" ;
    ProgrVP vp = insertObj (\\a => vp.ad ! a ++ vp.prp ++ vp.p ++ vp.s2 ! a) (predAux auxBe) ;
}
