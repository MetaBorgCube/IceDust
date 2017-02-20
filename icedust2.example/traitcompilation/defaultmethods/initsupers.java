import lib.icedust.*;
import java.util.Collection;
import java.util.Date;
import java.util.HashSet;
import javax.lang.model.type.NullType;

class initsupers  
{ 
  public static void main(String[] args)
  { 
    UseCountTen twenty = new UseCountTen();
    maintainCaches();
    { 
      Integer var1 = UseCountTen.getTen(twenty);
      System.out.println(var1);
    }
    { 
      Integer var1 = UseCountTen.getTwenty(twenty);
      System.out.println(var1);
    }
  }

  private static void maintainCaches()
  { 
    boolean notEmpty;
    notEmpty = true;
    while(notEmpty)
    { 
      notEmpty = false;
      CountTen.updateAllTenCache();
      notEmpty = notEmpty || CountTen.hasDirtyTen();
    }
    notEmpty = true;
    while(notEmpty)
    { 
      notEmpty = false;
      UseCountTen.updateAllTwentyCache();
      notEmpty = notEmpty || UseCountTen.hasDirtyTwenty();
    }
  }
}

class CountTen${
  public static Collection<CountTen> dirtyTen = new HashSet<CountTen>();
}

interface CountTen  
{ 
//  public CountTen () 
//  { 
//    CountTen.flagDirtyTen(this);
//  }

  default void init(){
    CountTen.flagDirtyTen(this);
  }
  
  default void updateTen_cache()
  { 
    setCacheTen(calculateTen());
  }

  public static boolean hasDirtyTen()
  { 
    return !CountTen$.dirtyTen.isEmpty();
  }

  public static void updateAllTenCache()
  { 
    Collection<CountTen> ens = CountTen$.dirtyTen;
    CountTen$.dirtyTen = new HashSet<CountTen>();
    if(ens.size() > 0)
    { 
      System.out.println("Updating " + "CountTen.ten" + ": " + ens.size());
    }
    for(CountTen en : ens)
    { 
      en.updateTen_cache();
    }
  }

  default void setCacheTen(Integer en)
  { 
    setCacheIncrementalTen(en);
  }

  default void addCacheIncrementalTen(Integer en)
  { 
    setCacheIncrementalTen(en);
  }

  default void removeCacheIncrementalTen(Integer en)
  { 
    setCacheIncrementalTen(null);
  }

  default void setCacheIncrementalTen(Integer en)
  { 
    Integer oldValue = this.getTen();
    this.setInternalCacheTen(en);
    Integer
    newValue = this.getTen();
    if(!Expressions.nullSafeEqual(oldValue, newValue))
    { 
      dirtyFlagFlowstoTen();
    }
  }

  public static Integer getTen(CountTen en)
  { 
    return en == null ? null : en.getTen();
  }

  public static Collection<Integer> getTen(Collection<CountTen> ens)
  { 
    Collection<Integer> result = Expressions.emptyCollection();
    for(CountTen en : ens)
    { 
      if(en.getTen() != null)
        result.add(en.getTen());
    }
    return result;
  }

  default Integer getTen()
  { 
    return getCalculatedTen();
  }

  default Integer getCalculatedTen()
  { 
    return getInternalCacheTen();
  }

  default Integer calculateTen()
  { 
    Integer var1 = Expressions.plus_Integer(1, 2);
    Integer var2 = Expressions.plus_Integer(var1, 3);
    Integer var3 = Expressions.plus_Integer(var2, 4);
    return var3;
  }

  default void dirtyFlagFlowstoTen()
  { 
    { 
      UseCountTen var1 = Expressions.filterType(this, UseCountTen.class);
      UseCountTen.flagDirtyTwenty(var1);
    }
  }

  public static void flagDirtyTen(CountTen en)
  { 
    if(en != null)
      CountTen$.dirtyTen.add(en);
  }

  public static void flagDirtyTen(Collection<CountTen> ens)
  { 
    CountTen$.dirtyTen.addAll(ens);
  }

  public Integer getInternalCacheTen();
  public void setInternalCacheTen(Integer ten);
//  protected Integer cacheTen;

//  public static Collection<CountTen> dirtyTen = new HashSet<CountTen>();
}

class UseCountTen implements CountTen
{ 
  public UseCountTen () 
  { 
    init();
//    CountTen.flagDirtyTen(this);
//    UseCountTen.flagDirtyTwenty(this);
  }
  
  public void init(){
    CountTen.super.init();
    UseCountTen.flagDirtyTwenty(this);
  }

//  protected void updateTen_cache()
//  { 
//    setCacheTen(calculateTen());
//  }
//
//  public static boolean hasDirtyTen()
//  { 
//    return !dirtyTen.isEmpty();
//  }
//
//  public static void updateAllTenCache()
//  { 
//    Collection<CountTen> ens = dirtyTen;
//    dirtyTen = new HashSet<CountTen>();
//    if(ens.size() > 0)
//    { 
//      System.out.println("Updating " + "CountTen.ten" + ": " + ens.size());
//    }
//    for(CountTen en : ens)
//    { 
//      en.updateTen_cache();
//    }
//  }
//
//  public void setCacheTen(Integer en)
//  { 
//    setCacheIncrementalTen(en);
//  }
//
//  protected void addCacheIncrementalTen(Integer en)
//  { 
//    setCacheIncrementalTen(en);
//  }
//
//  protected void removeCacheIncrementalTen(Integer en)
//  { 
//    setCacheIncrementalTen(null);
//  }
//
//  protected void setCacheIncrementalTen(Integer en)
//  { 
//    Integer oldValue = this.getTen();
//    this.cacheTen = en;
//    Integer
//    newValue = this.getTen();
//    if(!Expressions.nullSafeEqual(oldValue, newValue))
//    { 
//      dirtyFlagFlowstoTen();
//    }
//  }
//
  public static Integer getTen(CountTen en)
  { 
    return en == null ? null : en.getTen();
  }

  public static Collection<Integer> getTen(Collection<CountTen> ens)
  { 
    Collection<Integer> result = Expressions.emptyCollection();
    for(CountTen en : ens)
    { 
      if(en.getTen() != null)
        result.add(en.getTen());
    }
    return result;
  }
//
//  public Integer getTen()
//  { 
//    return getCalculatedTen();
//  }
//
//  private Integer getCalculatedTen()
//  { 
//    return cacheTen;
//  }
//
//  private Integer calculateTen()
//  { 
//    Integer var1 = Expressions.plus_Integer(1, 2);
//    Integer var2 = Expressions.plus_Integer(var1, 3);
//    Integer var3 = Expressions.plus_Integer(var2, 4);
//    return var3;
//  }
//
//  public void dirtyFlagFlowstoTen()
//  { 
//    { 
//      UseCountTen var1 = Expressions.filterType(this, UseCountTen.class);
//      UseCountTen.flagDirtyTwenty(var1);
//    }
//  }
//
//  protected static void flagDirtyTen(CountTen en)
//  { 
//    if(en != null)
//      dirtyTen.add(en);
//  }
//
//  protected static void flagDirtyTen(Collection<CountTen> ens)
//  { 
//    dirtyTen.addAll(ens);
//  }

  public Integer getInternalCacheTen(){return cacheTen;}
  public void setInternalCacheTen(Integer i){cacheTen = i;}
  protected Integer cacheTen;

//  private static Collection<CountTen> dirtyTen = new HashSet<CountTen>();

  protected void updateTwenty_cache()
  { 
    setCacheTwenty(calculateTwenty());
  }

  public static boolean hasDirtyTwenty()
  { 
    return !dirtyTwenty.isEmpty();
  }

  public static void updateAllTwentyCache()
  { 
    Collection<UseCountTen> ens = dirtyTwenty;
    dirtyTwenty = new HashSet<UseCountTen>();
    if(ens.size() > 0)
    { 
      System.out.println("Updating " + "UseCountTen.twenty" + ": " + ens.size());
    }
    for(UseCountTen en : ens)
    { 
      en.updateTwenty_cache();
    }
  }

  public void setCacheTwenty(Integer en)
  { 
    setCacheIncrementalTwenty(en);
  }

  protected void addCacheIncrementalTwenty(Integer en)
  { 
    setCacheIncrementalTwenty(en);
  }

  protected void removeCacheIncrementalTwenty(Integer en)
  { 
    setCacheIncrementalTwenty(null);
  }

  protected void setCacheIncrementalTwenty(Integer en)
  { 
    this.cacheTwenty = en;
  }

  public static Integer getTwenty(UseCountTen en)
  { 
    return en == null ? null : en.getTwenty();
  }

  public static Collection<Integer> getTwenty(Collection<UseCountTen> ens)
  { 
    Collection<Integer> result = Expressions.emptyCollection();
    for(UseCountTen en : ens)
    { 
      if(en.getTwenty() != null)
        result.add(en.getTwenty());
    }
    return result;
  }

  public Integer getTwenty()
  { 
    return getCalculatedTwenty();
  }

  private Integer getCalculatedTwenty()
  { 
    return cacheTwenty;
  }

  private Integer calculateTwenty()
  { 
    Integer var1 = this.getTen();
    Integer var2 = Expressions.mul_Integer(var1, 2);
    return var2;
  }

  public void dirtyFlagFlowstoTwenty()
  { }

  protected static void flagDirtyTwenty(UseCountTen en)
  { 
    if(en != null)
      dirtyTwenty.add(en);
  }

  protected static void flagDirtyTwenty(Collection<UseCountTen> ens)
  { 
    dirtyTwenty.addAll(ens);
  }

  protected Integer cacheTwenty;

  private static Collection<UseCountTen> dirtyTwenty = new HashSet<UseCountTen>();
}