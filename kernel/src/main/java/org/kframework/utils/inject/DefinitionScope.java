// Copyright (c) 2015 K Team. All Rights Reserved.
package org.kframework.utils.inject;

import static com.google.common.base.Preconditions.checkState;

import java.io.File;
import java.util.LinkedHashMap;
import java.util.Map;

import com.google.common.collect.Maps;
import com.google.inject.Key;
import com.google.inject.OutOfScopeException;
import com.google.inject.Provider;
import com.google.inject.Scope;
import com.google.inject.Scopes;

public class DefinitionScope implements Scope {

    private final InheritableThreadLocal<File> currentDefinitionId = new InheritableThreadLocal<>();

    private final LinkedHashMap<File, Map<Key<?>, Object>> values = new LinkedHashMap<File, Map<Key<?>, Object>>() {
        protected boolean removeEldestEntry(Map.Entry<File, Map<Key<?>, Object>> eldest) {
            return size() > Runtime.getRuntime().availableProcessors() * 2;
        }
    };

    public void enter(File definitionId) {
        checkState(currentDefinitionId.get() == null, "A scoping block is already in progress");
        currentDefinitionId.set(definitionId);
    }

    public void exit() {
        checkState(currentDefinitionId.get() != null, "No scoping block in progress");
        currentDefinitionId.remove();
    }

    @Override
    public <T> Provider<T> scope(Key<T> key, Provider<T> unscoped) {
        return new Provider<T>() {
            public T get() {
              Map<Key<?>, Object> scopedObjects = getScopedObjectMap(key);

              synchronized(scopedObjects) {
                  @SuppressWarnings("unchecked")
                  T current = (T) scopedObjects.get(key);
                  if (current == null && !scopedObjects.containsKey(key)) {
                    current = unscoped.get();

                    // don't remember proxies; these exist only to serve circular dependencies
                    if (Scopes.isCircularProxy(current)) {
                      return current;
                    }

                    scopedObjects.put(key, current);
                  }
                  return current;
              }
            }
          };
    }

    private <T> Map<Key<?>, Object> getScopedObjectMap(Key<T> key) {
        File definitionId = currentDefinitionId.get();
        if (definitionId == null) {
          throw new OutOfScopeException("Cannot access " + key
              + " outside of a scoping block");
        }
        synchronized(values) {
            Map<Key<?>, Object> scopedObjects = values.get(definitionId);
            if (scopedObjects == null) {
                scopedObjects = Maps.newHashMap();
                values.put(definitionId, scopedObjects);
            }
            return scopedObjects;
        }
      }

}
