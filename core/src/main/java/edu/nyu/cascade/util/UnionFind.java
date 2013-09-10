package edu.nyu.cascade.util;

import static com.google.common.base.Preconditions.checkArgument;

import java.io.Serializable;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.ImmutableCollection;
import com.google.common.collect.ImmutableList;
import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableSet;
import com.google.common.collect.Maps;
import com.google.common.collect.Multimaps;
import com.google.common.collect.SetMultimap;
import com.google.common.collect.Sets;

/**
 * A partitioning of a fixed set of elements into disjoint sets which can be efficiently merged.
 * See <a href="http://en.wikipedia.org/wiki/Disjoint-set_data_structure">this Wikipedia
 * article</a> for details.
 * 
 * <p>This data structure is not thread safe.
 * 
 * @author Louis Wasserman
 */
public class UnionFind<E> implements Serializable {
  
  private static final long serialVersionUID = -3117077679908893056L;

  public static class Partition implements Serializable {
    
    private static final long serialVersionUID = -632873777884295946L;
    
    private transient Partition parent;
    private transient int rank;

    public Partition() {
      this.parent = this;
      this.rank = 0;
    }

    public Partition findRoot() {
      Partition current = this;
      Partition next = current.parent;
      while (next != current) {
        current.parent = next.parent;
        current = next;
        next = next.parent;
      }
      return current;
    }

    public boolean union(Partition p) {
      Partition rep = findRoot();
      Partition pRep = p.findRoot();
      if (rep == pRep) {
        return false;
      } else if (rep.rank < pRep.rank) {
        rep.parent = pRep;
      } else if (rep.rank > pRep.rank) {
        pRep.parent = rep;
      } else {
        rep.parent = pRep;
        pRep.rank++;
      }
      return true;
    }

    @Override
    public int hashCode() {
      return System.identityHashCode(findRoot());
    }

    @Override
    public boolean equals(Object obj) {
      Preconditions.checkArgument(obj != null);
      if (obj instanceof Partition) {
        Partition other = (Partition) obj;
        return findRoot() == other.findRoot();
      }
      return false;
    }

    @Override
    public String toString() {
      if (parent == this) {
        return super.toString();
      } else {
        return findRoot().toString();
      }
    }

    Object writeReplace() {
      return findRoot();
    }

    private Object readResolve() {
      return new Partition();
    }
  }

  public static <E> UnionFind<E> create() {
    Map<E, Partition> map = Maps.newLinkedHashMap();
    return new UnionFind<E>(map, 0);
  }
  
  public static <E> UnionFind<E> create(Iterable<? extends E> elements) {
    ImmutableMap.Builder<E, Partition> builder = ImmutableMap.builder();
    LinkedHashSet<E> elementSet = Sets.newLinkedHashSet(elements);
    for (E e : elementSet) {
      builder.put(e, new Partition());
    }
    return new UnionFind<E>(builder.build(), elementSet.size());
  }

  private final Map<E, Partition> map;
  private int nPartitions = 0;

  private UnionFind(Map<E, Partition> map, int parts) {
    this.map = map;
  }
  
  public void add(E element, Partition p) {
    map.put(element, p);
    nPartitions++;
  }

  public Partition get(E element) {
    Partition p = map.get(element);
    checkArgument(p != null, "%s is not in the union find structure", element);
    return p;
  }

  public boolean union(E a, E b) {
    Partition aPart = get(a);
    Partition bPart = get(b);
    return union(aPart, bPart);
  }
  
  public boolean union(Partition aPart, Partition bPart) {
    if (aPart.union(bPart)) {
      nPartitions--;
      return true;
    }
    return false;
  }

  public ImmutableCollection<Set<E>> snapshot() {
//    SetMultimap<Partition, E> parts = Multimaps.invertFrom(
//        Multimaps.forMap(map),
//        HashMultimap.<Partition, E> create(
//            nPartitions,
//            map.size() / nPartitions + 1));
    SetMultimap<Partition, E> parts = Multimaps.invertFrom(
        Multimaps.forMap(map),
        HashMultimap.<Partition, E> create());
    ImmutableList.Builder<Set<E>> builder = ImmutableList.builder();
    for (Collection<E> partition : parts.asMap().values()) {
      builder.add(ImmutableSet.copyOf(partition));
    }
    return builder.build();
  }
}
