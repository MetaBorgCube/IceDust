import lib.icedust.*;
import java.util.Collection;
import java.util.Date;
import java.util.HashSet;
import javax.lang.model.type.NullType;

class relationwithtrait  
{ 
  public static void main(String[] args)
  { 
    Page page1 = new Page();
    Page page2 = new Page();
    Picture pic1 = new Picture();
    Picture pic2 = new Picture();
    page1.addPictures(pic1);
    page2.addPictures(pic1);
    page2.addPictures(pic2);
    pic1.setPath("/usr/local/pic1.gif");
    pic1.addUsedBy(page1);
    pic1.addUsedBy(page2);
    pic2.setPath("/usr/local/pic2.jpeg");
    pic2.addUsedBy(page2);
    maintainCaches();
    { 
      System.out.println("page1");
    }
    { 
      String var1 = Page.getDisplay(page1);
      System.out.println(var1);
    }
    { 
      System.out.println("page2");
    }
    { 
      String var1 = Page.getDisplay(page2);
      System.out.println(var1);
    }
  }

  private static void maintainCaches()
  { 
    boolean notEmpty;
  }
}

class HasPictures  
{ 
  public HasPictures () 
  { }

  public void addPictures(Picture en)
  { 
    Collection<Picture> newValue = Expressions.emptyCollection();
    newValue.addAll(this.pictures);
    newValue.add(en);
    setPictures(newValue);
  }

  public void addPictures(Collection<Picture> en)
  { 
    Collection<Picture> newValue = Expressions.emptyCollection();
    newValue.addAll(this.pictures);
    newValue.addAll(en);
    setPictures(newValue);
  }

  public void removePictures(Picture en)
  { 
    Collection<Picture> newValue = Expressions.emptyCollection();
    newValue.addAll(this.pictures);
    newValue.remove(en);
    setPictures(newValue);
  }

  public void removePictures(Collection<Picture> en)
  { 
    Collection<Picture> newValue = Expressions.emptyCollection();
    newValue.addAll(this.pictures);
    newValue.removeAll(en);
    setPictures(newValue);
  }

  public void setPictures(Collection<Picture> en)
  { 
    Collection<Picture> toAdd = new HashSet<Picture>();
    toAdd.addAll(en);
    toAdd.removeAll(pictures);
    Collection<Picture> toRemove = new HashSet<Picture>();
    toRemove.addAll(pictures);
    toRemove.removeAll(en);
    for(Picture n : toRemove)
    { 
      n.removeIncrementalUsedBy(this);
    }
    for(Picture n : toAdd)
    { 
      n.addIncrementalUsedBy(this);
    }
    setIncrementalPictures(en);
  }

  protected void addIncrementalPictures(Picture en)
  { 
    Collection<Picture> newValue = Expressions.emptyCollection();
    newValue.addAll(this.pictures);
    newValue.add(en);
    setIncrementalPictures(newValue);
  }

  protected void removeIncrementalPictures(Picture en)
  { 
    Collection<Picture> newValue = Expressions.emptyCollection();
    newValue.addAll(this.pictures);
    newValue.remove(en);
    setIncrementalPictures(newValue);
  }

  protected void setIncrementalPictures(Collection<Picture> en)
  { 
    this.pictures = en;
  }

  public static Collection<Picture> getPictures(HasPictures en)
  { 
    Collection<Picture> empty = Expressions.emptyCollection();
    return en == null ? empty : en.getPictures();
  }

  public static Collection<Picture> getPictures(Collection<HasPictures> ens)
  { 
    Collection<Picture> result = Expressions.emptyCollection();
    for(HasPictures en : ens)
    { 
      result.addAll(en.getPictures());
    }
    return result;
  }

  public Collection<Picture> getPictures()
  { 
    return pictures;
  }

  public void dirtyFlagFlowstoPictures()
  { }

  protected Collection<Picture> pictures = Expressions.emptyCollection();
}

class Page extends HasPictures
{ 
  public Page () 
  { }

  public static String getDisplay(Page en)
  { 
    return en == null ? null : en.getDisplay();
  }

  public static Collection<String> getDisplay(Collection<Page> ens)
  { 
    Collection<String> result = Expressions.emptyCollection();
    for(Page en : ens)
    { 
      if(en.getDisplay() != null)
        result.add(en.getDisplay());
    }
    return result;
  }

  public String getDisplay()
  { 
    return getCalculatedDisplay();
  }

  private String getCalculatedDisplay()
  { 
    return calculateDisplay();
  }

  private String calculateDisplay()
  { 
    Collection<Picture> var1 = this.getPictures();
    Collection<String> var2 = Picture.getPath(var1);
    String var3 = Expressions.concat(var2);
    return var3;
  }

  public void dirtyFlagFlowstoDisplay()
  { }

//  public void addPictures(Picture en)
//  { 
//    Collection<Picture> newValue = Expressions.emptyCollection();
//    newValue.addAll(this.pictures);
//    newValue.add(en);
//    setPictures(newValue);
//  }
//
//  public void addPictures(Collection<Picture> en)
//  { 
//    Collection<Picture> newValue = Expressions.emptyCollection();
//    newValue.addAll(this.pictures);
//    newValue.addAll(en);
//    setPictures(newValue);
//  }
//
//  public void removePictures(Picture en)
//  { 
//    Collection<Picture> newValue = Expressions.emptyCollection();
//    newValue.addAll(this.pictures);
//    newValue.remove(en);
//    setPictures(newValue);
//  }
//
//  public void removePictures(Collection<Picture> en)
//  { 
//    Collection<Picture> newValue = Expressions.emptyCollection();
//    newValue.addAll(this.pictures);
//    newValue.removeAll(en);
//    setPictures(newValue);
//  }
//
//  public void setPictures(Collection<Picture> en)
//  { 
//    Collection<Picture> toAdd = new HashSet<Picture>();
//    toAdd.addAll(en);
//    toAdd.removeAll(pictures);
//    Collection<Picture> toRemove = new HashSet<Picture>();
//    toRemove.addAll(pictures);
//    toRemove.removeAll(en);
//    for(Picture n : toRemove)
//    { 
//      n.removeIncrementalUsedBy(this);
//    }
//    for(Picture n : toAdd)
//    { 
//      n.addIncrementalUsedBy(this);
//    }
//    setIncrementalPictures(en);
//  }
//
//  protected void addIncrementalPictures(Picture en)
//  { 
//    Collection<Picture> newValue = Expressions.emptyCollection();
//    newValue.addAll(this.pictures);
//    newValue.add(en);
//    setIncrementalPictures(newValue);
//  }
//
//  protected void removeIncrementalPictures(Picture en)
//  { 
//    Collection<Picture> newValue = Expressions.emptyCollection();
//    newValue.addAll(this.pictures);
//    newValue.remove(en);
//    setIncrementalPictures(newValue);
//  }
//
//  protected void setIncrementalPictures(Collection<Picture> en)
//  { 
//    this.pictures = en;
//  }
//
//  public static Collection<Picture> getPictures(HasPictures en)
//  { 
//    Collection<Picture> empty = Expressions.emptyCollection();
//    return en == null ? empty : en.getPictures();
//  }
//
//  public static Collection<Picture> getPictures(Collection<HasPictures> ens)
//  { 
//    Collection<Picture> result = Expressions.emptyCollection();
//    for(HasPictures en : ens)
//    { 
//      result.addAll(en.getPictures());
//    }
//    return result;
//  }
//
//  public Collection<Picture> getPictures()
//  { 
//    return pictures;
//  }
//
//  public void dirtyFlagFlowstoPictures()
//  { }
//
//  protected Collection<Picture> pictures = Expressions.emptyCollection();
}

class Picture  
{ 
  public Picture () 
  { }

  public void setPath(String en)
  { 
    setIncrementalPath(en);
  }

  protected void addIncrementalPath(String en)
  { 
    setIncrementalPath(en);
  }

  protected void removeIncrementalPath(String en)
  { 
    setIncrementalPath(null);
  }

  protected void setIncrementalPath(String en)
  { 
    this.path = en;
  }

  public static String getPath(Picture en)
  { 
    return en == null ? null : en.getPath();
  }

  public static Collection<String> getPath(Collection<Picture> ens)
  { 
    Collection<String> result = Expressions.emptyCollection();
    for(Picture en : ens)
    { 
      if(en.getPath() != null)
        result.add(en.getPath());
    }
    return result;
  }

  public String getPath()
  { 
    return path;
  }

  public void dirtyFlagFlowstoPath()
  { }

  protected String path;

  public void addUsedBy(HasPictures en)
  { 
    Collection<HasPictures> newValue = Expressions.emptyCollection();
    newValue.addAll(this.usedBy);
    newValue.add(en);
    setUsedBy(newValue);
  }

  public void addUsedBy(Collection<HasPictures> en)
  { 
    Collection<HasPictures> newValue = Expressions.emptyCollection();
    newValue.addAll(this.usedBy);
    newValue.addAll(en);
    setUsedBy(newValue);
  }

  public void removeUsedBy(HasPictures en)
  { 
    Collection<HasPictures> newValue = Expressions.emptyCollection();
    newValue.addAll(this.usedBy);
    newValue.remove(en);
    setUsedBy(newValue);
  }

  public void removeUsedBy(Collection<HasPictures> en)
  { 
    Collection<HasPictures> newValue = Expressions.emptyCollection();
    newValue.addAll(this.usedBy);
    newValue.removeAll(en);
    setUsedBy(newValue);
  }

  public void setUsedBy(Collection<HasPictures> en)
  { 
    Collection<HasPictures> toAdd = new HashSet<HasPictures>();
    toAdd.addAll(en);
    toAdd.removeAll(usedBy);
    Collection<HasPictures> toRemove = new HashSet<HasPictures>();
    toRemove.addAll(usedBy);
    toRemove.removeAll(en);
    for(HasPictures n : toRemove)
    { 
      n.removeIncrementalPictures(this);
    }
    for(HasPictures n : toAdd)
    { 
      n.addIncrementalPictures(this);
    }
    setIncrementalUsedBy(en);
  }

  protected void addIncrementalUsedBy(HasPictures en)
  { 
    Collection<HasPictures> newValue = Expressions.emptyCollection();
    newValue.addAll(this.usedBy);
    newValue.add(en);
    setIncrementalUsedBy(newValue);
  }

  protected void removeIncrementalUsedBy(HasPictures en)
  { 
    Collection<HasPictures> newValue = Expressions.emptyCollection();
    newValue.addAll(this.usedBy);
    newValue.remove(en);
    setIncrementalUsedBy(newValue);
  }

  protected void setIncrementalUsedBy(Collection<HasPictures> en)
  { 
    this.usedBy = en;
  }

  public static Collection<HasPictures> getUsedBy(Picture en)
  { 
    Collection<HasPictures> empty = Expressions.emptyCollection();
    return en == null ? empty : en.getUsedBy();
  }

  public static Collection<HasPictures> getUsedBy(Collection<Picture> ens)
  { 
    Collection<HasPictures> result = Expressions.emptyCollection();
    for(Picture en : ens)
    { 
      result.addAll(en.getUsedBy());
    }
    return result;
  }

  public Collection<HasPictures> getUsedBy()
  { 
    return usedBy;
  }

  public void dirtyFlagFlowstoUsedBy()
  { }

  protected Collection<HasPictures> usedBy = Expressions.emptyCollection();
}