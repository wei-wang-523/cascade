package edu.nyu.cascade.c.preprocessor.steensfs;

import java.util.Map;
import java.util.Map.Entry;

import com.google.common.collect.Range;
import com.google.common.collect.RangeMap;
import com.google.common.collect.TreeRangeMap;

class FieldRangeMap<K extends Comparable<?>, V> implements RangeMap<K, V> {
	private TreeRangeMap<K, V> treeRangeMap;
	
	private FieldRangeMap() {
		treeRangeMap = TreeRangeMap.create();
	}
	
	public static <K extends Comparable<?>, V> FieldRangeMap<K, V> create() {
    return new FieldRangeMap<K, V>();
  }
	
	@Override
  public V get(K key) {
	  return treeRangeMap.get(key);
  }

	@Override
  public Entry<Range<K>, V> getEntry(K key) {
	  return treeRangeMap.getEntry(key);
  }

	@Override
  public Range<K> span() {
	  return treeRangeMap.span();
  }

	@Override
  public void put(Range<K> range, V value) {
		treeRangeMap.put(range, value);
  }

	@Override
  public void putAll(RangeMap<K, V> rangeMap) {
		treeRangeMap.putAll(rangeMap);
  }

	@Override
  public void clear() {
		treeRangeMap.clear();  
	}

	@Override
  public void remove(Range<K> range) {
		treeRangeMap.remove(range);
  }

	@Override
  public Map<Range<K>, V> asMapOfRanges() {
	  return treeRangeMap.asMapOfRanges();
  }

	/**
	 * Return the entries whose range is connected with <code>range</code>
	 * @param range
	 * @return
	 */
	@Override
  public RangeMap<K, V> subRangeMap(Range<K> range) {
		RangeMap<K, V> subMap = TreeRangeMap.create();
		
		for(Entry<Range<K>, V> entry : treeRangeMap.asMapOfRanges().entrySet()) {
			Range<K> entryRange = entry.getKey();
			if(entryRange.isConnected(range)) {
				if(!entryRange.intersection(range).isEmpty()) 
					subMap.put(entryRange, entry.getValue());
			}
		}
		
	  return subMap;
  }
	
	@Override
	public String toString() {
		return treeRangeMap.toString();
	}
}
