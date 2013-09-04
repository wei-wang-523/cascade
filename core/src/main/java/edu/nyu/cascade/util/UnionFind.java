package edu.nyu.cascade.util;

import java.util.Map;

import com.google.common.base.Preconditions;

/**
 * Union find algorithm to performs two useful operations of union and 
 * find in disjoint-set data structure
 * @author Wei
 *
 */
public class UnionFind {
  public static <T> Map<T, T> makeSet(Map<T, T> parentMap, T x) {
    Preconditions.checkArgument(!parentMap.containsKey(x));
    parentMap.put(x, x);
    return parentMap;
  }
  
  public static <T> T find(Map<T, T> parentMap, T x) {
    Preconditions.checkArgument(parentMap.containsKey(x));
    T parent = parentMap.get(x);
    if(!parent.equals(x))
      parent = find(parentMap, parent);
    return parent;
  }
  
  public static <T> Map<T, T> union(Map<T, T> parentMap, T x, T y) {
    if(!parentMap.containsKey(x))   parentMap = makeSet(parentMap, x);
    if(!parentMap.containsKey(y))   parentMap = makeSet(parentMap, y);
    T xRoot = find(parentMap, x);
    T yRoot = find(parentMap, y);
    if(xRoot.equals(yRoot)) return parentMap;
    
    parentMap.put(xRoot, yRoot);
    return parentMap;
  }
  
  private static <T> Pair<Map<T, T>, T> normalize(Map<T, T> parentMap, T x) {
    Preconditions.checkArgument(parentMap.containsKey(x));
    T parent = parentMap.get(x);
    if(!parent.equals(x)) {
      Pair<Map<T, T>, T> pair = normalize(parentMap, parent);
      parentMap = pair.fst();
      parent = pair.snd();
      parentMap.put(x, parent);
    }
    return Pair.of(parentMap, parent);
  }
  
  /**
   * Normalize @param parentMap, make the value of key is the root in the parentMap
   * @return normalized parentMap
   */
  public static <T> Map<T, T> normalizeMap(Map<T, T> parentMap) {
    for(T key : parentMap.keySet()) {
      Pair<Map<T, T>, T> pair = normalize(parentMap, key);
      parentMap = pair.fst();
    }
    return parentMap;
  }
}
