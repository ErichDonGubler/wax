use std::marker::PhantomData;

pub trait TreeIterator: Iterator {
    fn skip_tree(&mut self);

    fn filter_tree<F>(self, f: F) -> FilterTree<Self, (), F>
    where
        Self: Sized,
        F: FnMut(&Self::Item) -> Option<FilterTarget>,
    {
        FilterTree::new(self, f)
    }

    fn filter_tree_some<F>(self, f: F) -> FilterTree<Self, OptionSome, F>
    where
        Self: Sized,
        OptionSome: Projection<Self::Item>,
        F: FnMut(&<OptionSome as Projection<Self::Item>>::Output) -> Option<FilterTarget>,
    {
        FilterTree::new(self, f)
    }

    fn filter_tree_ok<F>(self, f: F) -> FilterTree<Self, ResultOk, F>
    where
        Self: Sized,
        ResultOk: Projection<Self::Item>,
        F: FnMut(&<ResultOk as Projection<Self::Item>>::Output) -> Option<FilterTarget>,
    {
        FilterTree::new(self, f)
    }
}

pub trait Projection<T> {
    type Output;

    fn project(item: &T) -> Option<&Self::Output>;
}

impl<T> Projection<T> for () {
    type Output = T;

    fn project(item: &T) -> Option<&Self::Output> {
        Some(item)
    }
}

pub enum OptionSome {}

impl<T> Projection<Option<T>> for OptionSome {
    type Output = T;

    fn project(option: &Option<T>) -> Option<&Self::Output> {
        option.as_ref()
    }
}

pub enum ResultOk {}

impl<T, E> Projection<Result<T, E>> for ResultOk {
    type Output = T;

    fn project(result: &Result<T, E>) -> Option<&Self::Output> {
        result.as_ref().ok()
    }
}

#[derive(Clone, Copy, Debug)]
pub enum FilterTarget {
    Children,
    Root,
    Tree,
}

#[derive(Debug)]
pub struct FilterTree<I, P, F> {
    items: I,
    f: F,
    phantom: PhantomData<fn() -> P>,
}

impl<I, P, F> FilterTree<I, P, F> {
    fn new(items: I, f: F) -> Self
    where
        I: TreeIterator,
        P: Projection<I::Item>,
        F: FnMut(&P::Output) -> Option<FilterTarget>,
    {
        FilterTree {
            items,
            f,
            phantom: PhantomData,
        }
    }
}

impl<I, P, F> Clone for FilterTree<I, P, F>
where
    I: Clone,
    F: Clone,
{
    fn clone(&self) -> Self {
        FilterTree {
            items: self.items.clone(),
            f: self.f.clone(),
            phantom: PhantomData,
        }
    }
}

impl<I, P, F> Copy for FilterTree<I, P, F>
where
    I: Copy,
    F: Copy,
{
}

impl<I, P, F> Iterator for FilterTree<I, P, F>
where
    I: TreeIterator,
    P: Projection<I::Item>,
    F: FnMut(&P::Output) -> Option<FilterTarget>,
{
    type Item = I::Item;

    fn next(&mut self) -> Option<Self::Item> {
        while let Some(item) = self.items.next() {
            if let Some(projection) = P::project(&item) {
                match (self.f)(projection) {
                    None => {
                        return Some(item);
                    },
                    Some(FilterTarget::Children) => {
                        self.items.skip_tree();
                        return Some(item);
                    },
                    Some(FilterTarget::Root) => {
                        continue;
                    },
                    Some(FilterTarget::Tree) => {
                        self.items.skip_tree();
                        continue;
                    },
                }
            }
            return Some(item);
        }
        return None;
    }
}
