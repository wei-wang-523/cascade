package edu.nyu.cascade.util;

import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import com.google.common.collect.Range;
import com.google.common.collect.RangeMap;
import com.google.common.collect.TreeRangeMap;

public class FieldRangeMap<K extends Comparable<?>, V> implements RangeMap<K, V> {
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
	public boolean equals(Object o) {
		if(!(o instanceof FieldRangeMap)) return false;
		Map<Range<K>, V> thisMap = this.asMapOfRanges();
		@SuppressWarnings("unchecked")
		Map<Range<K>, V> thatMap = ((FieldRangeMap<K, V>) o).asMapOfRanges();
		if(thisMap.size() != thatMap.size()) return false;
		Iterator<Entry<Range<K>, V>> thisItr = thisMap.entrySet().iterator();
		Iterator<Entry<Range<K>, V>> thatItr = thatMap.entrySet().iterator();
		while(thisItr.hasNext() && thatItr.hasNext()) {
			Entry<Range<K>, V> thisEntry = thisItr.next();
			Entry<Range<K>, V> thatEntry = thatItr.next();
			if(!thisEntry.getKey().equals(thatEntry.getKey())) return false;
			if(!thisEntry.getValue().equals(thatEntry.getValue())) return false;
		}
		return true;
	}
	
	@Override
	public String toString() {
		return treeRangeMap.toString();
	}

	@Override
	public Map<Range<K>, V> asDescendingMapOfRanges() {
		// TODO Auto-generated method stub
		return null;
	}
}
